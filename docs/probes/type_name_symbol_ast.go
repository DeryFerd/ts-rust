package ast

import "slices"

func (c *DiagnosticsCollection) Wave150Unsorted(file string) []*Diagnostic {
	c.mu.Lock()
	defer c.mu.Unlock()
	return slices.Clone(c.fileDiagnostics[file])
}
