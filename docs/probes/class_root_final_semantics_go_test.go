package checker_test

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"testing"

	"github.com/microsoft/typescript-go/internal/ast"
	"github.com/microsoft/typescript-go/internal/bundled"
	"github.com/microsoft/typescript-go/internal/checker"
	"github.com/microsoft/typescript-go/internal/compiler"
	"github.com/microsoft/typescript-go/internal/core"
	"github.com/microsoft/typescript-go/internal/tsoptions"
	"github.com/microsoft/typescript-go/internal/vfs/vfstest"
)

type wave148RootCase struct {
	name, target string
	strict       bool
	files        map[string]string
	order        []string
	codes        []int32
}

func wave148RootProgram(t *testing.T, row wave148RootCase) (*checker.Checker, *compiler.Program) {
	t.Helper()
	lib, err := os.ReadFile(filepath.Join("..", "..", "_submodules", "TypeScript", "src", "lib", "es5.d.ts"))
	if err != nil {
		t.Fatal(err)
	}
	config, err := json.Marshal(struct {
		CompilerOptions map[string]any `json:"compilerOptions"`
		Files           []string       `json:"files"`
	}{
		map[string]any{"noLib": true, "skipLibCheck": true, "noEmit": true, "target": row.target, "strict": row.strict},
		append([]string{"es5.d.ts"}, row.order...),
	})
	if err != nil {
		t.Fatal(err)
	}
	files := map[string]string{
		"/project/es5.d.ts":      string(lib),
		"/project/tsconfig.json": string(config),
	}
	for name, source := range row.files {
		files["/project/"+name] = source
	}
	fs := vfstest.FromMap(files, true)
	host := compiler.NewCompilerHost("/project", fs, bundled.LibPath(), nil, nil)
	parsed, errors := tsoptions.GetParsedCommandLineOfConfigFile("/project/tsconfig.json", &core.CompilerOptions{}, nil, host, nil)
	if len(errors) != 0 {
		t.Fatalf("config errors: %v", errors)
	}
	program := compiler.NewProgram(compiler.ProgramOptions{Config: parsed, Host: host})
	program.BindSourceFiles()
	query, done := program.GetTypeChecker(t.Context())
	t.Cleanup(done)
	return query, program
}

func TestWave148ClassRootComposition(t *testing.T) {
	rows := []wave148RootCase{
		{
			name: "forwarded_parameter", target: "es5", order: []string{"input.ts"},
			files: map[string]string{"input.ts": "class Base { constructor(public value: string) {} } class Model extends Base { constructor(value: string) { super(value); } }"},
			codes: []int32{},
		},
		{
			name: "local_body", target: "es5", order: []string{"input.ts"},
			files: map[string]string{"input.ts": "class Model { constructor() { const value = 1; } }"},
			codes: []int32{},
		},
		{
			name: "missing_super", target: "es5", order: []string{"input.ts"},
			files: map[string]string{"input.ts": "class Base {} class Model extends Base { constructor() {} }"},
			codes: []int32{2377},
		},
		{
			name: "retained_earlier", target: "es5", order: []string{"first.ts", "later.ts"},
			files: map[string]string{"first.ts": `const first: number = "wrong";`, "later.ts": "class Later { method(value: string) {} }"},
			codes: []int32{2322},
		},
		{
			name: "script_static_name", target: "es5", order: []string{"input.ts"},
			files: map[string]string{"input.ts": "class C { static foo: string; bar() { let k = foo; } }"},
			codes: []int32{2662},
		},
		{
			name: "exported_static_name", target: "es5", order: []string{"input.ts"},
			files: map[string]string{"input.ts": "export class C { static foo: string; bar() { let k = foo; } }"},
			codes: []int32{2662},
		},
		{
			name: "duplicate_property", target: "esnext", strict: true, order: []string{"input.ts"},
			files: map[string]string{"input.ts": "class Model { value: number = 1; value: number = 2; }"},
			codes: []int32{2300, 2300},
		},
		{
			name: "duplicate_initializer", target: "esnext", strict: true, order: []string{"input.ts"},
			files: map[string]string{"input.ts": "class Model { value: number = 2; accessor value: string = 'next'; }"},
			codes: []int32{2300, 2322, 2300},
		},
	}
	for _, static := range []string{"", "static"} {
		for _, visibility := range [][2]string{{"private", "public"}, {"public", "protected"}} {
			code := int32(2415)
			if static != "" {
				code = 2417
			}
			rows = append(rows, wave148RootCase{
				name:   fmt.Sprintf("visibility_%s_%s_%s", static, visibility[0], visibility[1]),
				target: "es5", order: []string{"input.ts"},
				files: map[string]string{"input.ts": fmt.Sprintf(
					"class Base { %s %s value = 1; } class Derived extends Base { %s %s value = 2; }",
					visibility[0], static, visibility[1], static,
				)},
				codes: []int32{code},
			})
		}
	}
	for _, row := range rows {
		t.Run(row.name, func(t *testing.T) {
			query, program := wave148RootProgram(t, row)
			read := func() map[string][]wave146Diagnostic {
				result := map[string][]wave146Diagnostic{}
				for _, name := range row.order {
					result[name] = wave146Diagnostics(query.GetDiagnostics(t.Context(), program.GetSourceFile("/project/"+name)))
				}
				return result
			}
			cold := read()
			codes := []int32{}
			for _, name := range row.order {
				for _, diagnostic := range cold[name] {
					codes = append(codes, diagnostic.Code)
				}
			}
			if !reflect.DeepEqual(codes, row.codes) {
				t.Fatalf("codes=%v expected=%v records=%v", codes, row.codes, cold)
			}
			types := map[*ast.Node]*checker.Type{}
			for _, name := range row.order {
				wave146Walk(program.GetSourceFile("/project/"+name).AsNode(), func(node *ast.Node) {
					if node.Kind == ast.KindClassDeclaration && node.Name() != nil {
						types[node.Name()] = query.GetTypeAtLocation(node.Name())
					}
				})
			}
			for range 2 {
				if warm := read(); !reflect.DeepEqual(warm, cold) {
					t.Fatalf("diagnostics changed: %v", warm)
				}
				for node, type_ := range types {
					if query.GetTypeAtLocation(node) != type_ {
						t.Fatalf("class identity changed: %s", node.Text())
					}
				}
			}
			encoded, err := json.Marshal(cold)
			if err != nil {
				t.Fatal(err)
			}
			t.Log(string(encoded))
		})
	}
}
