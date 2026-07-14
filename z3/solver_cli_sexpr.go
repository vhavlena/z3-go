//go:build cgo
// +build cgo

package z3

import (
	"fmt"
	"strings"
)

// splitTopLevelForms splits s into its top-level "(...)" forms, treating
// text inside "..." strings and |...| quoted symbols as opaque so parens
// there don't confuse the depth count. Anything outside a top-level form
// (whitespace between forms) is discarded.
func splitTopLevelForms(s string) []string {
	var forms []string
	depth := 0
	start := -1
	inStr, inPipe := false, false
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case inStr:
			if c == '"' {
				if i+1 < len(s) && s[i+1] == '"' {
					i++
				} else {
					inStr = false
				}
			}
		case inPipe:
			if c == '|' {
				inPipe = false
			}
		case c == '"':
			inStr = true
		case c == '|':
			inPipe = true
		case c == '(':
			if depth == 0 {
				start = i
			}
			depth++
		case c == ')':
			depth--
			if depth == 0 && start >= 0 {
				forms = append(forms, s[start:i+1])
				start = -1
			}
		}
	}
	return forms
}

// topLevelChildren splits a single "(...)" form into its immediate,
// depth-0 child tokens - each either a bare atom or a full nested "(...)"
// form, kept as its original source text. It does not recurse further.
func topLevelChildren(form string) []string {
	form = strings.TrimSpace(form)
	if len(form) < 2 || form[0] != '(' || form[len(form)-1] != ')' {
		return nil
	}
	inner := form[1 : len(form)-1]

	var children []string
	depth := 0
	start := -1
	inStr, inPipe := false, false
	flush := func(end int) {
		if start != -1 {
			children = append(children, inner[start:end])
			start = -1
		}
	}
	for i := 0; i < len(inner); i++ {
		c := inner[i]
		switch {
		case inStr:
			if c == '"' {
				if i+1 < len(inner) && inner[i+1] == '"' {
					i++
				} else {
					inStr = false
				}
			}
		case inPipe:
			if c == '|' {
				inPipe = false
			}
		case c == '"':
			if start == -1 {
				start = i
			}
			inStr = true
		case c == '|':
			if start == -1 {
				start = i
			}
			inPipe = true
		case c == '(':
			if depth == 0 && start == -1 {
				start = i
			}
			depth++
		case c == ')':
			depth--
		case c == ' ' || c == '\t' || c == '\n' || c == '\r':
			if depth == 0 {
				flush(i)
			}
		default:
			if depth == 0 && start == -1 {
				start = i
			}
		}
	}
	flush(len(inner))
	return children
}

// nonAssertPreamble returns script with every top-level command that isn't a
// declaration/definition dropped - i.e. keeps sort/datatype/function
// declarations and define-funs, drops assert/check-sat/push/pop/etc.
func nonAssertPreamble(script string) string {
	var b strings.Builder
	for _, form := range splitTopLevelForms(script) {
		children := topLevelChildren(form)
		if len(children) == 0 {
			continue
		}
		switch children[0] {
		case "assert", "check-sat", "check-sat-assuming", "get-value",
			"get-model", "push", "pop", "set-option", "exit", "reset":
			continue
		default:
			b.WriteString(form)
			b.WriteByte('\n')
		}
	}
	return b.String()
}

// reconstructModel turns the response to "(get-value (names...))" - a
// top-level list of (name value) pairs - into a genuine *Model by replaying
// each pair as an equality assertion (alongside the original declarations,
// but none of the original, possibly-hard assertions) against a fresh,
// trivial native solver. Returns nil if the response can't be parsed or the
// replay doesn't check out as sat, matching Solver.Model's nil-on-failure
// convention.
func reconstructModel(ctx *Context, declScript string, getValueOutput string) *Model {
	getValueOutput = strings.TrimSpace(getValueOutput)
	if getValueOutput == "" || getValueOutput[0] != '(' {
		return nil
	}
	pairs := topLevelChildren(getValueOutput)
	if len(pairs) == 0 {
		return nil
	}

	var eq strings.Builder
	eq.WriteString(nonAssertPreamble(declScript))
	replayed := 0
	for _, pf := range pairs {
		kv := topLevelChildren(pf)
		if len(kv) != 2 {
			continue
		}
		fmt.Fprintf(&eq, "(assert (= %s %s))\n", kv[0], kv[1])
		replayed++
	}
	if replayed == 0 {
		return nil
	}

	verify := ctx.NewSimpleSolver()
	defer verify.Close()
	if err := verify.AssertSMTLIB2String(eq.String()); err != nil {
		return nil
	}
	res, err := verify.Check()
	if err != nil || res != Sat {
		return nil
	}
	return verify.Model()
}
