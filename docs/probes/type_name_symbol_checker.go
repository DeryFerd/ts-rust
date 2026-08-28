package checker

import "github.com/microsoft/typescript-go/internal/ast"

func (c *Checker) Wave150SymbolCounts() [2]int {
	return [2]int{len(c.unresolvedSymbols), len(c.errorTypes)}
}

func (c *Checker) Wave150Diagnostics(file string) []*ast.Diagnostic {
	return c.diagnostics.Wave150Unsorted(file)
}
