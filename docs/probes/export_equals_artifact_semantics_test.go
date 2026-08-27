package checker_test

import (
	"encoding/json"
	"os"
	"reflect"
	"slices"
	"testing"

	"github.com/microsoft/typescript-go/internal/ast"
	"github.com/microsoft/typescript-go/internal/bundled"
	"github.com/microsoft/typescript-go/internal/checker"
	"github.com/microsoft/typescript-go/internal/compiler"
	"github.com/microsoft/typescript-go/internal/core"
	"github.com/microsoft/typescript-go/internal/tsoptions"
	"github.com/microsoft/typescript-go/internal/vfs/vfstest"
)

type wave147ExportCase struct {
	Name, Main, ExportFile string
	Files                  map[string]string
	Codes                  []int32
	DifferentFromRead      bool
}

type wave147ExportQuery struct {
	Type         string   `json:"type"`
	Symbol       string   `json:"symbol"`
	Declarations []string `json:"declarations"`
	Alias        bool     `json:"alias"`
}

func TestWave147ExportEqualsArtifacts(t *testing.T) {
	contents, err := os.ReadFile(os.Getenv("TS_EXPORT_REVIEW_CASES"))
	if err != nil {
		t.Fatal(err)
	}
	var cases []wave147ExportCase
	if err := json.Unmarshal(contents, &cases); err != nil {
		t.Fatal(err)
	}
	observations := make([]map[string]any, 0, len(cases))
	for _, row := range cases {
		t.Run(row.Name, func(t *testing.T) {
			if row.Main == "" {
				row.Main = "input.ts"
			}
			if row.ExportFile == "" {
				row.ExportFile = row.Main
			}
			files := map[string]string{}
			for name, content := range row.Files {
				files["/project/"+name] = content
			}
			config, err := json.Marshal(map[string]any{
				"compilerOptions": map[string]any{"module": "nodenext", "target": "esnext", "strict": true, "noEmit": true, "lib": []string{"es5"}, "types": []string{}},
				"files":           []string{row.Main},
			})
			if err != nil {
				t.Fatal(err)
			}
			files["/project/tsconfig.json"] = string(config)
			fs := bundled.WrapFS(vfstest.FromMap(files, true))
			host := compiler.NewCompilerHost("/project", fs, bundled.LibPath(), nil, nil)
			parsed, errors := tsoptions.GetParsedCommandLineOfConfigFile("/project/tsconfig.json", nil, nil, host, nil)
			if parsed == nil || len(errors) != 0 {
				t.Fatalf("config diagnostics: %v", errors)
			}
			program := compiler.NewProgram(compiler.ProgramOptions{Config: parsed, Host: host, SingleThreaded: core.TSTrue})
			program.BindSourceFiles()
			c, done := program.GetTypeChecker(t.Context())
			t.Cleanup(done)
			main := program.GetSourceFile("/project/" + row.Main)
			exportFile := program.GetSourceFile("/project/" + row.ExportFile)
			if main == nil || exportFile == nil {
				t.Fatal("a requested source was not loaded")
			}
			diagnostics := c.GetDiagnostics(t.Context(), main)
			var codes, related []int32
			for _, diagnostic := range diagnostics {
				codes = append(codes, diagnostic.Code())
				for _, detail := range diagnostic.RelatedInformation() {
					related = append(related, detail.Code())
				}
			}
			if !slices.Equal(codes, row.Codes) {
				t.Fatalf("diagnostics %v, expected %v", codes, row.Codes)
			}
			if row.Name == "original_invocation" && !slices.Equal(related, []int32{7038}) {
				t.Fatalf("invocation detail changed: %v", related)
			}
			var exported, read, call *ast.Node
			var visit func(*ast.Node) bool
			visit = func(node *ast.Node) bool {
				if ast.IsExportAssignment(node) && ast.GetSourceFileOfNode(node) == exportFile {
					exported = node.Expression()
				}
				if ast.IsVariableDeclaration(node) && node.Name().Text() == "observed" {
					read = node.Initializer()
				}
				if ast.IsCallExpression(node) && ast.GetSourceFileOfNode(node) == main {
					call = node
				}
				return node.ForEachChild(visit)
			}
			exportFile.ForEachChild(visit)
			if exportFile != main {
				main.ForEachChild(visit)
			}
			if exported == nil {
				t.Fatal("missing export assignment")
			}
			query := func(node *ast.Node) wave147ExportQuery {
				value := c.GetTypeAtLocation(node)
				result := wave147ExportQuery{Type: c.TypeToStringEx(value, node.Parent, checker.TypeFormatFlagsNoTruncation, nil)}
				if symbol := c.GetSymbolAtLocation(node); symbol != nil {
					result.Symbol = c.SymbolToString(symbol)
					result.Alias = symbol.Flags&ast.SymbolFlagsAlias != 0
					for _, declaration := range symbol.Declarations {
						result.Declarations = append(result.Declarations, declaration.Kind.String())
					}
				}
				return result
			}
			value, symbol := c.GetTypeAtLocation(exported), c.GetSymbolAtLocation(exported)
			if symbol == nil {
				t.Fatal("export symbol did not resolve")
			}
			if ast.IsIdentifier(exported) {
				expected := c.GetDeclaredTypeOfSymbol(symbol)
				if expected == c.GetErrorType() {
					expected = c.GetTypeOfSymbol(symbol)
				}
				if value != expected {
					t.Fatal("export assignment did not use its declared-or-value symbol type")
				}
			}
			observation := map[string]any{"name": row.Name, "export": query(exported), "codes": codes, "related": related}
			if read != nil {
				observation["read"] = query(read)
				if row.DifferentFromRead && c.GetTypeAtLocation(read) == value {
					t.Fatal("ordinary expression type did not differ from the export query")
				}
			}
			if call != nil {
				observation["call"] = query(call)
				observation["callee"] = query(call.Expression())
				if row.Name == "original_invocation" && c.GetTypeAtLocation(call) != c.GetErrorType() {
					t.Fatal("failed invocation lost the canonical error type")
				}
			}
			before := query(exported)
			for range 3 {
				if c.GetTypeAtLocation(exported) != value || c.GetSymbolAtLocation(exported) != symbol || !reflect.DeepEqual(query(exported), before) || !reflect.DeepEqual(c.GetDiagnostics(t.Context(), main), diagnostics) {
					t.Fatal("warm artifact query changed type, symbol, or diagnostics")
				}
			}
			observations = append(observations, observation)
			t.Logf("export=%+v ordinary_read=%v", before, observation["read"])
		})
	}
	data, err := json.MarshalIndent(observations, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(os.Getenv("TS_EXPORT_REVIEW_GO_REPORT"), data, 0o644); err != nil {
		t.Fatal(err)
	}
}
