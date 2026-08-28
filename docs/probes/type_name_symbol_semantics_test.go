package checker_test

import (
	"encoding/json"
	"os"
	"reflect"
	"testing"

	"github.com/microsoft/typescript-go/internal/ast"
	"github.com/microsoft/typescript-go/internal/bundled"
	"github.com/microsoft/typescript-go/internal/compiler"
	"github.com/microsoft/typescript-go/internal/core"
	"github.com/microsoft/typescript-go/internal/tsoptions"
	"github.com/microsoft/typescript-go/internal/vfs/vfstest"
)

func TestWave150TypeNameMeaning(t *testing.T) {
	const original = "import { forwarded as local } from './target';\nimport * as Types from './target';\ndeclare const result: Types.Exposed;\n"
	const originalTarget = "declare const value: number;\nexport { value as forwarded };\n"
	const valueTarget = "declare const value: number;\nexport { value as forwarded, value as Exposed };\n"
	const valueQuery = "import { forwarded as local } from './target';\nimport * as Types from './target';\ndeclare const result: typeof Types.Exposed;\n"
	const importerPath = "/project/importer.d.ts"
	var observations []map[string]any
	for _, test := range []struct {
		name, importer, target, typeText string
		unresolved                       bool
		code                             int32
	}{
		{"original_value_export_as_type_source", original, originalTarget, "Types.Exposed", true, 2694},
		{"reexported_value_as_type", original, valueTarget, "Types.Exposed", true, 2749},
		{"reexported_value_typeof", valueQuery, valueTarget, "number", false, 0},
	} {
		t.Run(test.name, func(t *testing.T) {
			config := `{"compilerOptions":{"noLib":true,"strict":true,"noEmit":true,"module":"commonjs","types":[]},"files":["/project/importer.d.ts","/project/target.d.ts"]}`
			fs := bundled.WrapFS(vfstest.FromMap(map[string]string{
				importerPath: test.importer, "/project/target.d.ts": test.target, "/project/tsconfig.json": config,
			}, true))
			host := compiler.NewCompilerHost("/project", fs, bundled.LibPath(), nil, nil)
			parsed, errors := tsoptions.GetParsedCommandLineOfConfigFile("/project/tsconfig.json", nil, nil, host, nil)
			if parsed == nil || len(errors) != 0 {
				t.Fatalf("invalid config: %v", errors)
			}
			program := compiler.NewProgram(compiler.ProgramOptions{Host: host, Config: parsed, SingleThreaded: core.TSTrue})
			program.BindSourceFiles()
			c, done := program.GetTypeChecker(t.Context())
			defer done()
			var annotation *ast.Node
			var visit func(*ast.Node) bool
			visit = func(node *ast.Node) bool {
				if ast.IsVariableDeclaration(node) && node.Name().Text() == "result" {
					annotation = node.Type()
				}
				node.ForEachChild(visit)
				return false
			}
			visit(program.GetSourceFile(importerPath).AsNode())
			if annotation == nil {
				t.Fatal("result annotation is absent")
			}
			var name *ast.Node
			if ast.IsTypeReferenceNode(annotation) {
				name = annotation.AsTypeReferenceNode().TypeName
			} else {
				name = annotation.AsTypeQueryNode().ExprName
			}
			before := c.Wave150SymbolCounts()
			symbol := c.GetSymbolAtLocation(name)
			afterSymbol := c.Wave150SymbolCounts()
			if symbol == nil || (symbol.CheckFlags&ast.CheckFlagsUnresolved != 0) != test.unresolved {
				t.Fatalf("unexpected name symbol: %+v", symbol)
			}
			if afterSymbol[1] != before[1] || len(c.Wave150Diagnostics(importerPath)) != 0 {
				t.Fatal("symbol query created an error type or diagnostic")
			}
			if test.unresolved && (symbol.Flags != ast.SymbolFlagsTypeAlias|ast.SymbolFlagsTransient || symbol.CheckFlags != ast.CheckFlagsUnresolved || len(symbol.Declarations) != 0) {
				t.Fatalf("wrong unresolved symbol fields: %+v", symbol)
			}
			value := c.GetTypeFromTypeNode(annotation)
			if actual := c.TypeToString(value); actual != test.typeText {
				t.Fatalf("type=%q, expected %q", actual, test.typeText)
			}
			diagnostics := c.Wave150Diagnostics(importerPath)
			var codes []int32
			for _, diagnostic := range diagnostics {
				codes = append(codes, diagnostic.Code())
			}
			if test.code == 0 && len(codes) != 0 || test.code != 0 && !reflect.DeepEqual(codes, []int32{test.code}) {
				t.Fatalf("diagnostic codes=%v, expected %d", codes, test.code)
			}
			if c.GetSymbolAtLocation(name) != symbol || c.GetTypeFromTypeNode(annotation) != value || !reflect.DeepEqual(c.Wave150Diagnostics(importerPath), diagnostics) {
				t.Fatal("warm identities or diagnostics changed")
			}
			observation := map[string]any{
				"name": test.name, "importer": test.importer, "target": test.target,
				"symbol": c.SymbolToString(symbol), "symbolFlags": symbol.Flags, "checkFlags": symbol.CheckFlags,
				"unresolved": test.unresolved, "type": c.TypeToString(value), "diagnosticCodes": codes,
				"before": before, "afterSymbol": afterSymbol, "warmStable": true,
			}
			observations = append(observations, observation)
			t.Logf("symbol=%q unresolved=%v type=%q diagnostics=%v", c.SymbolToString(symbol), test.unresolved, c.TypeToString(value), codes)
		})
	}
	if output := os.Getenv("TS_WAVE150_GO_REPORT"); output != "" {
		data, err := json.MarshalIndent(observations, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(output, append(data, '\n'), 0600); err != nil {
			t.Fatal(err)
		}
	}
}
