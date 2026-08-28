package checker_test

import (
	"encoding/json"
	"fmt"
	"os"
	"reflect"
	"sort"
	"strings"
	"testing"

	"github.com/microsoft/typescript-go/internal/ast"
	"github.com/microsoft/typescript-go/internal/bundled"
	"github.com/microsoft/typescript-go/internal/checker"
	"github.com/microsoft/typescript-go/internal/compiler"
	"github.com/microsoft/typescript-go/internal/core"
	"github.com/microsoft/typescript-go/internal/scanner"
	"github.com/microsoft/typescript-go/internal/tsoptions"
	"github.com/microsoft/typescript-go/internal/vfs/vfstest"
)

type mergedExportFile struct {
	Path string `json:"path"`
	Text string `json:"text"`
}

type mergedExportCase struct {
	Name      string             `json:"name"`
	Consumer  string             `json:"consumer"`
	ClassFile string             `json:"classFile"`
	Expect    string             `json:"expect"`
	Files     []mergedExportFile `json:"files"`
}

func mergedNode(node *ast.Node) any {
	if node == nil {
		return nil
	}
	file := ast.GetSourceFileOfNode(node)
	start := scanner.GetTokenPosOfNode(node, file, false)
	return map[string]any{
		"file": strings.TrimPrefix(file.FileName(), "/project/"),
		"kind": node.Kind.String(), "start": start, "end": node.End(),
		"text": file.Text()[start:node.End()],
	}
}

func mergedSymbol(c *checker.Checker, symbol *ast.Symbol) any {
	if symbol == nil {
		return nil
	}
	symbol = c.GetMergedSymbol(symbol)
	declarations := make([]any, 0, len(symbol.Declarations))
	for _, declaration := range symbol.Declarations {
		declarations = append(declarations, mergedNode(declaration))
	}
	return map[string]any{
		"name":         c.SymbolToString(symbol),
		"flags":        uint64(symbol.Flags &^ ast.SymbolFlagsTransient),
		"transient":    symbol.Flags&ast.SymbolFlagsTransient != 0,
		"declarations": declarations, "valueDeclaration": mergedNode(symbol.ValueDeclaration),
	}
}

func mergedDiagnostic(diagnostic *ast.Diagnostic) any {
	var message func(*ast.Diagnostic, int) string
	message = func(current *ast.Diagnostic, depth int) string {
		text := strings.Repeat("  ", depth) + current.String()
		for _, child := range current.MessageChain() {
			text += "\n" + message(child, depth+1)
		}
		return text
	}
	var file any
	if diagnostic.File() != nil {
		file = strings.TrimPrefix(diagnostic.File().FileName(), "/project/")
	}
	related := make([]any, 0, len(diagnostic.RelatedInformation()))
	for _, child := range diagnostic.RelatedInformation() {
		related = append(related, mergedDiagnostic(child))
	}
	return map[string]any{
		"file": file, "start": diagnostic.Pos(), "end": diagnostic.End(),
		"code": diagnostic.Code(), "category": int(diagnostic.Category()),
		"message": message(diagnostic, 0), "related": related,
		"unnecessary": diagnostic.ReportsUnnecessary(), "deprecated": diagnostic.ReportsDeprecated(),
	}
}

func mergedTypeRole(type_, declared, value *checker.Type) string {
	if type_ == declared {
		return "declared"
	}
	if type_ == value {
		return "value"
	}
	return "other"
}

func mergedQuery(c *checker.Checker, node *ast.Node, owner *ast.Symbol, declared, value *checker.Type) any {
	type_ := c.GetTypeAtLocation(node)
	symbol := c.GetSymbolAtLocation(node)
	return map[string]any{
		"type":     c.TypeToStringEx(type_, node, checker.TypeFormatFlagsNoTruncation, nil),
		"typeRole": mergedTypeRole(type_, declared, value),
		"symbol":   mergedSymbol(c, symbol), "symbolIsOwner": c.GetMergedSymbol(symbol) == owner,
	}
}

func mergedMembers(c *checker.Checker, type_ *checker.Type, owner *ast.Symbol, enclosing *ast.Node) []any {
	properties := append([]*ast.Symbol(nil), c.GetPropertiesOfType(type_)...)
	sort.Slice(properties, func(i, j int) bool { return properties[i].Name < properties[j].Name })
	result := make([]any, 0, len(properties))
	for _, property := range properties {
		var declarationSymbolMatches any
		var typeDisplay any
		if len(property.Declarations) != 0 && property.Declarations[0].Name() != nil {
			declarationSymbolMatches = c.GetMergedSymbol(c.GetSymbolAtLocation(property.Declarations[0].Name())) == c.GetMergedSymbol(property)
		}
		if property.Name != "prototype" {
			typeDisplay = c.TypeToStringEx(c.GetTypeOfSymbol(property), enclosing, checker.TypeFormatFlagsNoTruncation, nil)
		}
		result = append(result, map[string]any{
			"name":                     property.Name,
			"type":                     typeDisplay,
			"symbol":                   mergedSymbol(c, property),
			"parentIsOwner":            c.GetMergedSymbol(property.Parent) == owner,
			"declarationSymbolMatches": declarationSymbolMatches,
		})
	}
	return result
}

func observeMergedExport(t *testing.T, row mergedExportCase, order string) (result map[string]any) {
	result = map[string]any{"name": row.Name, "order": order, "expect": row.Expect}
	defer func() {
		if failure := recover(); failure != nil {
			result["panic"] = fmt.Sprint(failure)
		}
	}()
	files := map[string]string{}
	roots := make([]string, 0, len(row.Files))
	for _, file := range row.Files {
		files["/project/"+file.Path] = file.Text
		roots = append(roots, file.Path)
	}
	config, err := json.Marshal(map[string]any{
		"compilerOptions": map[string]any{
			"module": "nodenext", "moduleResolution": "nodenext", "target": "esnext",
			"strict": false, "skipLibCheck": true, "noEmit": true,
			"lib": []string{"es5"}, "types": []string{},
		},
		"files": roots,
	})
	if err != nil {
		panic(err)
	}
	files["/project/tsconfig.json"] = string(config)
	fs := bundled.WrapFS(vfstest.FromMap(files, true))
	host := compiler.NewCompilerHost("/project", fs, bundled.LibPath(), nil, nil)
	parsed, errors := tsoptions.GetParsedCommandLineOfConfigFile("/project/tsconfig.json", nil, nil, host, nil)
	if parsed == nil || len(errors) != 0 {
		panic(fmt.Sprintf("config diagnostics: %v", errors))
	}
	program := compiler.NewProgram(compiler.ProgramOptions{Config: parsed, Host: host, SingleThreaded: core.TSTrue})
	program.BindSourceFiles()
	c, done := program.GetTypeChecker(t.Context())
	defer done()
	nodes := map[string]*ast.Node{}
	var class, exportStatement *ast.Node
	var reads, namespaces []string
	for _, input := range row.Files {
		file := program.GetSourceFile("/project/" + input.Path)
		if file == nil {
			panic("missing file " + input.Path)
		}
		namespaceIndex := 0
		var visit func(*ast.Node) bool
		visit = func(node *ast.Node) bool {
			if ast.IsClassDeclaration(node) && node.Name() != nil && node.Name().Text() == "Value" && input.Path == row.ClassFile {
				class = node
				nodes["class"] = node.Name()
			}
			if ast.IsModuleDeclaration(node) && node.Name().Text() == "Value" {
				role := fmt.Sprintf("namespace:%s:%d", input.Path, namespaceIndex)
				namespaceIndex++
				nodes[role] = node.Name()
				namespaces = append(namespaces, role)
			}
			if ast.IsExportAssignment(node) && input.Path == row.Consumer {
				exportStatement = node
				nodes["export"] = node.Expression()
			}
			if ast.IsVariableDeclaration(node) && input.Path == row.Consumer && node.Initializer() != nil && ast.IsIdentifier(node.Initializer()) && node.Initializer().Text() == "Value" {
				role := "read:" + node.Name().Text()
				nodes[role] = node.Initializer()
				reads = append(reads, role)
			}
			return node.ForEachChild(visit)
		}
		file.AsNode().ForEachChild(visit)
	}
	if class == nil || exportStatement == nil {
		panic("missing class or export assignment")
	}
	if order == "read-first" && len(reads) == 0 || order == "namespace-first" && len(namespaces) == 0 {
		result["skippedOrder"] = true
		return result
	}
	owner := c.GetMergedSymbol(class.Symbol())
	firstRole, firstKind := "export", "type"
	var firstType *checker.Type
	var firstSymbol *ast.Symbol
	switch order {
	case "read-first":
		firstRole = reads[0]
	case "class-first":
		firstRole = "class"
	case "namespace-first":
		firstRole = namespaces[0]
	case "symbol-first":
		firstKind = "symbol"
	case "alias-first":
		firstKind = "alias"
	}
	switch firstKind {
	case "type":
		firstType = c.GetTypeAtLocation(nodes[firstRole])
	case "symbol":
		firstSymbol = c.GetSymbolAtLocation(nodes[firstRole])
	case "alias":
		firstSymbol = c.GetAliasedSymbol(exportStatement.Symbol())
	}
	collectDiagnostics := func() []any {
		diagnostics := append([]*ast.Diagnostic(nil), program.GetConfigFileParsingDiagnostics()...)
		diagnostics = append(diagnostics, program.GetProgramDiagnostics()...)
		for _, input := range row.Files {
			file := program.GetSourceFile("/project/" + input.Path)
			diagnostics = append(diagnostics, program.GetSyntacticDiagnostics(t.Context(), file)...)
			if !program.SkipTypeChecking(file, false) {
				diagnostics = append(diagnostics, file.BindDiagnostics()...)
				diagnostics = append(diagnostics, c.GetDiagnostics(t.Context(), file)...)
			}
		}
		diagnostics = append(diagnostics, c.GetGlobalDiagnostics()...)
		result := make([]any, 0, len(diagnostics))
		for _, diagnostic := range compiler.SortAndDeduplicateDiagnostics(diagnostics) {
			result = append(result, mergedDiagnostic(diagnostic))
		}
		return result
	}
	diagnostics := collectDiagnostics()
	declared, value := c.GetDeclaredTypeOfSymbol(owner), c.GetTypeOfSymbol(owner)
	first := map[string]any{"role": firstRole, "kind": firstKind}
	if firstType != nil {
		first["type"] = c.TypeToStringEx(firstType, nodes[firstRole], checker.TypeFormatFlagsNoTruncation, nil)
		first["typeRole"] = mergedTypeRole(firstType, declared, value)
		first["stable"] = firstType == c.GetTypeAtLocation(nodes[firstRole])
	} else {
		first["symbol"] = mergedSymbol(c, firstSymbol)
		first["symbolIsOwner"] = c.GetMergedSymbol(firstSymbol) == owner
		if firstKind == "alias" {
			first["stable"] = firstSymbol == c.GetAliasedSymbol(exportStatement.Symbol())
		} else {
			first["stable"] = firstSymbol == c.GetSymbolAtLocation(nodes[firstRole])
		}
	}
	result["first"] = first
	snapshot := func() map[string]any {
		queries := map[string]any{}
		for role, node := range nodes {
			queries[role] = mergedQuery(c, node, owner, declared, value)
		}
		constructors := make([]any, 0)
		for _, signature := range c.GetSignaturesOfType(value, checker.SignatureKindConstruct) {
			constructors = append(constructors, map[string]any{
				"parameters":      len(signature.Parameters()),
				"returnsDeclared": c.GetReturnTypeOfSignature(signature) == declared,
			})
		}
		return map[string]any{
			"diagnostics": diagnostics, "owner": mergedSymbol(c, owner), "queries": queries,
			"types": map[string]any{
				"declared": c.TypeToStringEx(declared, nodes["export"], checker.TypeFormatFlagsNoTruncation, nil),
				"value":    c.TypeToStringEx(value, nodes["export"], checker.TypeFormatFlagsNoTruncation, nil),
				"distinct": declared != value,
			},
			"instanceMembers":    mergedMembers(c, declared, owner, nodes["export"]),
			"valueMembers":       mergedMembers(c, value, owner, nodes["export"]),
			"constructors":       constructors,
			"aliasTargetIsOwner": c.GetMergedSymbol(c.GetAliasedSymbol(exportStatement.Symbol())) == owner,
		}
	}
	before := snapshot()
	warm := true
	for range 2 {
		warm = warm && reflect.DeepEqual(collectDiagnostics(), diagnostics)
		warm = warm && c.GetDeclaredTypeOfSymbol(owner) == declared && c.GetTypeOfSymbol(owner) == value
		warm = warm && reflect.DeepEqual(snapshot(), before)
	}
	result["snapshot"], result["warmStable"], result["sourceStatus"] = before, warm, "checked"
	return result
}

func TestWave152MergedClassExportSemantics(t *testing.T) {
	contents, err := os.ReadFile(os.Getenv("TS_MERGED_EXPORT_CASES"))
	if err != nil {
		t.Fatal(err)
	}
	var cases []mergedExportCase
	if err := json.Unmarshal(contents, &cases); err != nil {
		t.Fatal(err)
	}
	observations := make([]any, 0)
	for _, row := range cases {
		for _, order := range []string{"export-first", "read-first", "symbol-first", "class-first", "namespace-first", "alias-first"} {
			observation := observeMergedExport(t, row, order)
			observations = append(observations, observation)
			if failure, present := observation["panic"]; present {
				t.Errorf("%s/%s: %v", row.Name, order, failure)
			}
			if stable, present := observation["warmStable"]; present && stable != true {
				t.Errorf("%s/%s: warm query changed", row.Name, order)
			}
		}
	}
	data, err := json.MarshalIndent(observations, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(os.Getenv("TS_MERGED_EXPORT_GO_REPORT"), data, 0o644); err != nil {
		t.Fatal(err)
	}
}
