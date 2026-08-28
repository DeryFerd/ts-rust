package checker_test

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"strings"
	"testing"

	"github.com/microsoft/typescript-go/internal/ast"
	"github.com/microsoft/typescript-go/internal/bundled"
	"github.com/microsoft/typescript-go/internal/checker"
	"github.com/microsoft/typescript-go/internal/compiler"
	"github.com/microsoft/typescript-go/internal/core"
	"github.com/microsoft/typescript-go/internal/locale"
	"github.com/microsoft/typescript-go/internal/tsoptions"
	"github.com/microsoft/typescript-go/internal/vfs/vfstest"
)

const wave146BooleanSource = "class BooleanAssignment { value?: number; source?: boolean; constructor(input: string) { const first: number = input; this.value = this.source; const after: number = this.value; } }"
const wave146ScalarSource = "class ScalarAssignment { value?: number; constructor(input: string) { this.value = input; const after: number = this.value; } }"

type wave146Diagnostic struct {
	Code    int32    `json:"code"`
	Start   int      `json:"start"`
	End     int      `json:"end"`
	Message string   `json:"message"`
	Details []string `json:"details"`
	Related int      `json:"related"`
}

func wave146Program(t *testing.T, source string, exact bool) (*checker.Checker, *ast.SourceFile) {
	t.Helper()
	lib, err := os.ReadFile(filepath.Join("..", "..", "_submodules", "TypeScript", "src", "lib", "es5.d.ts"))
	if err != nil {
		t.Fatal(err)
	}
	configText := fmt.Sprintf(`{"compilerOptions":{"noLib":true,"skipLibCheck":true,"strict":true,"noEmit":true,"target":"es2015","exactOptionalPropertyTypes":%t},"files":["es5.d.ts","input.ts"]}`, exact)
	fs := vfstest.FromMap(map[string]string{
		"/es5.d.ts":      string(lib),
		"/input.ts":      source,
		"/tsconfig.json": configText,
	}, true)
	host := compiler.NewCompilerHost("/", fs, bundled.LibPath(), nil, nil)
	config, errors := tsoptions.GetParsedCommandLineOfConfigFile("/tsconfig.json", &core.CompilerOptions{}, nil, host, nil)
	if len(errors) != 0 {
		t.Fatalf("config errors: %v", errors)
	}
	program := compiler.NewProgram(compiler.ProgramOptions{Config: config, Host: host})
	program.BindSourceFiles()
	query, done := program.GetTypeChecker(t.Context())
	t.Cleanup(done)
	return query, program.GetSourceFile("/input.ts")
}

func wave146Walk(node *ast.Node, visit func(*ast.Node)) {
	visit(node)
	node.ForEachChild(func(child *ast.Node) bool {
		wave146Walk(child, visit)
		return false
	})
}

func wave146Diagnostics(diagnostics []*ast.Diagnostic) []wave146Diagnostic {
	result := make([]wave146Diagnostic, 0, len(diagnostics))
	for _, diagnostic := range diagnostics {
		details := []string{}
		var appendDetails func([]*ast.Diagnostic, int)
		appendDetails = func(children []*ast.Diagnostic, depth int) {
			for _, child := range children {
				details = append(details, strings.Repeat("  ", depth)+child.Localize(locale.Default))
				appendDetails(child.MessageChain(), depth+1)
			}
		}
		appendDetails(diagnostic.MessageChain(), 1)
		result = append(result, wave146Diagnostic{
			Code: diagnostic.Code(), Start: diagnostic.Pos(), End: diagnostic.End(),
			Message: diagnostic.Localize(locale.Default), Details: details,
			Related: len(diagnostic.RelatedInformation()),
		})
	}
	return result
}

func TestWave146ClassWriteDiagnosticRecords(t *testing.T) {
	for _, row := range []struct {
		name, source string
		count        int
	}{{"boolean", wave146BooleanSource, 3}, {"scalar", wave146ScalarSource, 2}} {
		for _, exact := range []bool{false, true} {
			t.Run(fmt.Sprintf("%s_exact_%t", row.name, exact), func(t *testing.T) {
				query, file := wave146Program(t, row.source, exact)
				first := wave146Diagnostics(query.GetDiagnostics(t.Context(), file))
				if len(first) != row.count {
					t.Fatalf("diagnostic count: %v", first)
				}
				types := map[string]string{}
				wave146Walk(file.AsNode(), func(node *ast.Node) {
					if node.Kind == ast.KindVariableDeclaration && node.AsVariableDeclaration().Initializer != nil {
						types[node.Name().Text()] = query.TypeToString(query.GetTypeAtLocation(node.AsVariableDeclaration().Initializer))
					}
					if node.Kind == ast.KindBinaryExpression {
						binary := node.AsBinaryExpression()
						types["write_target"] = query.TypeToString(query.GetTypeAtLocation(binary.Left))
						types["write_source"] = query.TypeToString(query.GetTypeAtLocation(binary.Right))
					}
				})
				for range 2 {
					if got := wave146Diagnostics(query.GetDiagnostics(t.Context(), file)); !reflect.DeepEqual(got, first) {
						t.Fatalf("warm diagnostic change: %v", got)
					}
				}
				encoded, err := json.Marshal(struct {
					Diagnostics []wave146Diagnostic `json:"diagnostics"`
					Types       map[string]string   `json:"types"`
				}{first, types})
				if err != nil {
					t.Fatal(err)
				}
				t.Log(string(encoded))
			})
		}
	}
}

func TestWave146StringOptionalConstructorHistory(t *testing.T) {
	for _, write := range []string{"", "this.value = undefined;"} {
		for _, exact := range []bool{false, true} {
			for _, queryFirst := range []bool{false, true} {
				t.Run(fmt.Sprintf("write_%t_exact_%t_query_%t", write != "", exact, queryFirst), func(t *testing.T) {
					source := fmt.Sprintf("declare let unrelated: number | undefined; class StringHistory { constructor(public readonly value?: string) { %s const parameter = value; const field = this.value; } }", write)
					query, file := wave146Program(t, source, exact)
					if queryFirst {
						wave146Walk(file.AsNode(), func(node *ast.Node) {
							if node.Kind == ast.KindUnionType {
								if got := query.TypeToString(query.GetTypeFromTypeNode(node)); got != "number | undefined" {
									t.Fatalf("unrelated type: %s", got)
								}
							}
						})
					}
					if diagnostics := query.GetDiagnostics(t.Context(), file); len(diagnostics) != 0 {
						t.Fatalf("diagnostics: %v", wave146Diagnostics(diagnostics))
					}
					types := map[string]string{}
					wave146Walk(file.AsNode(), func(node *ast.Node) {
						if node.Kind == ast.KindVariableDeclaration && node.AsVariableDeclaration().Initializer != nil {
							types[node.Name().Text()] = query.TypeToString(query.GetTypeAtLocation(node.AsVariableDeclaration().Initializer))
						}
					})
					field := "string | undefined"
					if write != "" {
						field = "undefined"
					}
					if types["parameter"] != "string | undefined" || types["field"] != field {
						t.Fatalf("read types: %v", types)
					}
					for range 2 {
						if diagnostics := query.GetDiagnostics(t.Context(), file); len(diagnostics) != 0 {
							t.Fatalf("warm diagnostics: %v", diagnostics)
						}
					}
					t.Logf("diagnostics=0 parameter=%s field=%s", types["parameter"], types["field"])
				})
			}
		}
	}
}
