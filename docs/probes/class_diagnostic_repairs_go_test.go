package checker_test

import (
	"encoding/json"
	"reflect"
	"testing"

	"github.com/microsoft/typescript-go/internal/ast"
	"github.com/microsoft/typescript-go/internal/checker"
)

func TestWave150ClassDiagnosticRepairs(t *testing.T) {
	for _, row := range []struct {
		name, source, message string
		code                  int32
		start, end            int
	}{
		{
			name: "static_original", code: 2662, start: 46, end: 49,
			source:  "class C { static foo: string; bar() { let k = foo; } }",
			message: "Cannot find name 'foo'. Did you mean the static member 'C.foo'?",
		},
		{
			name: "exported_original", code: 2662, start: 53, end: 56,
			source:  "export class C { static foo: string; bar() { let k = foo; } }",
			message: "Cannot find name 'foo'. Did you mean the static member 'C.foo'?",
		},
		{
			name: "static_renamed", code: 2662, start: 84, end: 89,
			source:  "/* class */ class Catalog { static title: string; read() { let result = /* value */ title; } }",
			message: "Cannot find name 'title'. Did you mean the static member 'Catalog.title'?",
		},
		{
			name: "exported_renamed", code: 2662, start: 91, end: 96,
			source:  "export /* class */ class Catalog { static title: string; read() { let result = /* value */ title; } }",
			message: "Cannot find name 'title'. Did you mean the static member 'Catalog.title'?",
		},
		{
			name: "constructor_original", code: 2377, start: 41, end: 52,
			source:  "class Base {} class Model extends Base { constructor() {} }",
			message: "Constructors for derived classes must contain a 'super' call.",
		},
		{
			name: "constructor_comment", code: 2377, start: 66, end: 77,
			source:  "class Base {}\nclass Model extends Base {\n  /* constructor note */ constructor /* gap */ () {}\n}",
			message: "Constructors for derived classes must contain a 'super' call.",
		},
		{
			name: "constructor_public", code: 2377, start: 41, end: 59,
			source:  "class Base {} class Model extends Base { public constructor() {} }",
			message: "Constructors for derived classes must contain a 'super' call.",
		},
		{
			name: "constructor_public_block", code: 2377, start: 41, end: 82,
			source:  "class Base {} class Model extends Base { public /* constructor note */ constructor() {} }",
			message: "Constructors for derived classes must contain a 'super' call.",
		},
		{
			name: "constructor_public_line", code: 2377, start: 69, end: 80,
			source:  "class Base {} class Model extends Base { public // constructor note\n constructor() {} }",
			message: "Constructors for derived classes must contain a 'super' call.",
		},
	} {
		t.Run(row.name, func(t *testing.T) {
			query, program := wave148RootProgram(t, wave148RootCase{
				name: row.name, target: "es5", strict: false,
				files: map[string]string{"input.ts": row.source},
				order: []string{"input.ts"},
			})
			file := program.GetSourceFile("/project/input.ts")
			read := func() []wave146Diagnostic {
				return wave146Diagnostics(query.GetDiagnostics(t.Context(), file))
			}
			expected := []wave146Diagnostic{{
				Code: row.code, Start: row.start, End: row.end,
				Message: row.message, Details: []string{}, Related: 0,
			}}
			cold := read()
			if !reflect.DeepEqual(cold, expected) {
				t.Fatalf("records=%v expected=%v", cold, expected)
			}
			types := map[*ast.Node]*checker.Type{}
			var unresolved *ast.Node
			lineShapeChecked := false
			wave146Walk(file.AsNode(), func(node *ast.Node) {
				if row.code == 2377 && node.Kind == ast.KindClassDeclaration && node.Name() != nil {
					types[node.Name()] = query.GetTypeAtLocation(node.Name())
				}
				if row.code == 2662 && node.Kind == ast.KindVariableDeclaration {
					unresolved = node.AsVariableDeclaration().Initializer
				}
				if row.name == "constructor_public_line" && node.Kind == ast.KindClassDeclaration && node.Name() != nil && node.Name().Text() == "Model" {
					members := node.Members()
					if len(members) != 2 {
						t.Fatalf("expected a field and a constructor: %v", members)
					}
					field, constructor := members[0], members[1]
					if field.Kind != ast.KindPropertyDeclaration || field.Name() == nil || field.Name().Text() != "public" {
						t.Fatal("public must be a field name, not a constructor modifier")
					}
					if constructor.Kind != ast.KindConstructor || ast.HasSyntacticModifier(constructor, ast.ModifierFlagsPublic) {
						t.Fatal("the second member must be an unmodified constructor")
					}
					lineShapeChecked = true
				}
			})
			if row.code == 2662 && unresolved == nil {
				t.Fatal("the fixture must contain its unresolved name")
			}
			if row.name == "constructor_public_line" && !lineShapeChecked {
				t.Fatal("the line-break class must be checked")
			}
			for range 3 {
				if warm := read(); !reflect.DeepEqual(warm, cold) {
					t.Fatalf("diagnostics changed: %v", warm)
				}
				if unresolved != nil && query.GetSymbolAtLocation(unresolved) != nil {
					t.Fatal("the bare name must not bind to the static member")
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
