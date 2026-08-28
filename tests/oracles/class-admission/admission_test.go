package compiler_test

import (
	"encoding/json"
	"fmt"
	"reflect"
	"testing"

	"github.com/microsoft/typescript-go/internal/ast"
	"github.com/microsoft/typescript-go/internal/bundled"
	"github.com/microsoft/typescript-go/internal/compiler"
	"github.com/microsoft/typescript-go/internal/core"
	"github.com/microsoft/typescript-go/internal/locale"
	"github.com/microsoft/typescript-go/internal/tsoptions"
	"github.com/microsoft/typescript-go/internal/vfs/vfstest"
)

type classAdmissionDiagnostic struct {
	File    string `json:"file"`
	Code    int32  `json:"code"`
	Start   int    `json:"start"`
	End     int    `json:"end"`
	Message string `json:"message"`
}

func classAdmissionDiagnostics(input []*ast.Diagnostic) []classAdmissionDiagnostic {
	result := make([]classAdmissionDiagnostic, 0, len(input))
	for _, diagnostic := range input {
		result = append(result, classAdmissionDiagnostic{
			File: diagnostic.File().FileName(), Code: diagnostic.Code(),
			Start: diagnostic.Pos(), End: diagnostic.End(),
			Message: diagnostic.Localize(locale.Default),
		})
	}
	return result
}

func TestClassAdmissionRootExpectations(t *testing.T) {
	const constructorFile = "/project/class-second-wave.ts"
	for _, row := range []struct {
		name      string
		files     map[string]string
		roots     []string
		strict    bool
		library   bool
		className string
		expected  []int32
	}{
		{
			name: "primitive_super_forwarding",
			files: map[string]string{constructorFile: "class Base { constructor(public value: string) {} } " +
				"class Model extends Base { constructor(value: string) { super(value); } }"},
			roots: []string{constructorFile}, className: "Model", expected: []int32{},
		},
		{
			name:  "constructor_local",
			files: map[string]string{constructorFile: "class Model { constructor() { const value = 1; } }"},
			roots: []string{constructorFile}, className: "Model", expected: []int32{},
		},
		{
			name:  "missing_super",
			files: map[string]string{constructorFile: "class Base {} class Model extends Base { constructor() {} }"},
			roots: []string{constructorFile}, className: "Model", expected: []int32{2377},
		},
		{
			name: "later_method_keeps_earlier_diagnostic",
			files: map[string]string{
				"/project/first.ts": `const first: number = "wrong";`,
				"/project/later.ts": "class Later { method(value: string) {} }",
			},
			roots:  []string{"/project/first.ts", "/project/later.ts"},
			strict: true, library: true, expected: []int32{2322},
		},
	} {
		t.Run(row.name, func(t *testing.T) {
			// The direct checker fixtures bind no default library. Program binds es5.
			options := map[string]any{
				"strict": row.strict, "target": "es5", "module": "none",
				"noLib": !row.library,
			}
			if row.library {
				options["lib"] = []string{"es5"}
			}
			config, err := json.Marshal(map[string]any{
				"compilerOptions": options, "files": row.roots,
			})
			if err != nil {
				t.Fatal(err)
			}
			files := make(map[string]string, len(row.files)+1)
			for name, text := range row.files {
				files[name] = text
			}
			files["/project/tsconfig.json"] = string(config)
			fs := bundled.WrapFS(vfstest.FromMap(files, true))
			host := compiler.NewCompilerHost("/project", fs, bundled.LibPath(), nil, nil)
			parsed, errors := tsoptions.GetParsedCommandLineOfConfigFile(
				"/project/tsconfig.json", &core.CompilerOptions{}, nil, host, nil,
			)
			if len(errors) != 0 {
				t.Fatalf("config errors: %v", errors)
			}
			parsed.CompilerOptions().SingleThreaded = core.TSTrue
			program := compiler.NewProgram(compiler.ProgramOptions{Config: parsed, Host: host})
			program.BindSourceFiles()
			query, done := program.GetTypeChecker(t.Context())
			defer done()
			readDiagnostics := func() []classAdmissionDiagnostic {
				result := make([]classAdmissionDiagnostic, 0)
				for _, root := range row.roots {
					file := program.GetSourceFile(root)
					if file == nil {
						t.Fatalf("missing source %s", root)
					}
					if len(file.Diagnostics()) != 0 {
						t.Fatalf("parser diagnostics for %s: %v", root, file.Diagnostics())
					}
					result = append(result, classAdmissionDiagnostics(query.GetDiagnostics(t.Context(), file))...)
				}
				return result
			}
			cold := readDiagnostics()
			codes := make([]int32, 0, len(cold))
			for _, diagnostic := range cold {
				codes = append(codes, diagnostic.Code)
			}
			if !reflect.DeepEqual(codes, row.expected) {
				t.Fatalf("source diagnostics: %v", cold)
			}
			instanceName, valueName := "", ""
			if row.className != "" {
				var name *ast.Node
				for _, statement := range program.GetSourceFile(constructorFile).Statements.Nodes {
					if statement.Kind == ast.KindClassDeclaration && statement.Name().Text() == row.className {
						name = statement.Name()
					}
				}
				if name == nil {
					t.Fatalf("missing class %s", row.className)
				}
				symbol := query.GetSymbolAtLocation(name)
				if symbol == nil {
					t.Fatal("missing class symbol")
				}
				instance := query.GetDeclaredTypeOfSymbol(symbol)
				value := query.GetTypeOfSymbol(symbol)
				instanceName, valueName = query.TypeToString(instance), query.TypeToString(value)
				if instanceName != row.className || valueName != "typeof "+row.className || instance == value {
					t.Fatalf("class types: instance=%s value=%s", instanceName, valueName)
				}
				for range 2 {
					if query.GetSymbolAtLocation(name) != symbol || query.GetDeclaredTypeOfSymbol(symbol) != instance ||
						query.GetTypeOfSymbol(symbol) != value || !reflect.DeepEqual(readDiagnostics(), cold) {
						t.Fatal("warm class identity or diagnostics changed")
					}
				}
			} else if !reflect.DeepEqual(readDiagnostics(), cold) {
				t.Fatal("warm program diagnostics changed")
			}
			proof, err := json.Marshal(map[string]any{
				"case": row.name, "sources": row.files, "options": options,
				"diagnostics": cold, "instance": instanceName, "value": valueName,
				"warmStable": true,
			})
			if err != nil {
				t.Fatal(err)
			}
			fmt.Println(string(proof))
		})
	}
}
