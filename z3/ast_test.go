//go:build cgo
// +build cgo

package z3

import "testing"

func TestASTTraversalFromSMTLIB(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	const script = `
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x 3) y))
(assert (= y 10))
`

	asts, err := ctx.ParseSMTLIB2String(script)
	if err != nil {
		t.Fatalf("ParseSMTLIB2String error: %v", err)
	}
	if len(asts) == 0 {
		t.Fatalf("expected parsed ASTs, got none")
	}

	s := ctx.NewSolver()
	defer s.Close()
	if err := s.AssertSMTLIB2String(script); err != nil {
		t.Fatalf("AssertSMTLIB2String error: %v", err)
	}

	var eq AST
	for _, node := range asts {
		if node.Kind() != ASTKindApp {
			continue
		}
		decl := node.Decl()
		if decl.Kind() == DeclOpEq {
			left := node.Child(0)
			if left.IsApp() && left.Decl().Kind() == DeclOpAdd {
				eq = node
				break
			}
		}
	}
	if eq.a == nil {
		t.Fatalf("failed to locate equality AST in parsed script")
	}

	left := eq.Child(0)
	right := eq.Child(1)
	if !left.IsApp() || left.Decl().Kind() != DeclOpAdd {
		t.Fatalf("expected left child to be addition, got %s", left.String())
	}
	addChildren := left.Children()
	if len(addChildren) != 2 {
		t.Fatalf("expected addition to expose 2 children, got %d", len(addChildren))
	}
	if addChildren[0].Decl().Name() != "x" {
		t.Fatalf("expected first summand to be x, got %s", addChildren[0].String())
	}
	if val, ok := addChildren[1].AsInt64(); !ok || val != 3 {
		t.Fatalf("expected numeric literal 3, got %s (ok=%v)", addChildren[1].String(), ok)
	}
	if right.Decl().Name() != "y" {
		t.Fatalf("expected right-hand side to be y, got %s", right.String())
	}

	var walkKinds []ASTKind
	left.Walk(func(node AST) bool {
		walkKinds = append(walkKinds, node.Kind())
		return true
	})
	if len(walkKinds) == 0 {
		t.Fatalf("Walk did not visit any nodes")
	}

	res, err := s.Check()
	if err != nil {
		t.Fatalf("solver check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
	m := s.Model()
	if m == nil {
		t.Fatalf("expected model from solver")
	}
	defer m.Close()

	x := ctx.Const("x", ctx.IntSort())
	xVal := m.Eval(x, true)
	if xVal.a == nil {
		t.Fatalf("model evaluation for x returned nil")
	}
	var traversed string
	xVal.Walk(func(node AST) bool {
		if node.Kind() == ASTKindNumeral {
			traversed = node.NumeralString()
		}
		return true
	})
	if traversed != "7" {
		t.Fatalf("expected to discover model value 7 via traversal, got %s", traversed)
	}
	if v, ok := xVal.AsInt64(); !ok || v != 7 {
		t.Fatalf("AsInt64 expected 7, got %d (ok=%v)", v, ok)
	}
}

func TestASTModelValueFromDatatype(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	const script = `
(declare-datatypes ()
  ((OAtom
    (OString (str String))
    (ONumber (num Int))
    (OBoolean (bool Bool))
    ONull
    OUndef))
)

(declare-datatypes (T)
  ((OGenType
    (Atom (atom OAtom))
    (OObj (obj (Array String T)))
    (OArray (arr (Array Int T)))))
)

(declare-datatypes ()
  ((OGenTypeAtom (Atom (atom OAtom))))
)

(define-sort OTypeD0 () (OGenType OGenTypeAtom))

(declare-fun str_val () OTypeD0)
(assert (is-OString (atom str_val)))
(assert (= (str (atom str_val)) "hello world"))
`

	s := ctx.NewSolver()
	defer s.Close()
	asts, err := ctx.ParseSMTLIB2String(script)
	if err != nil {
		t.Fatalf("ParseSMTLIB2String error: %v", err)
	}
	var strRef AST
	for _, f := range asts {
		found := false
		f.Walk(func(node AST) bool {
			if node.IsApp() && node.NumChildren() == 0 {
				if decl := node.Decl(); decl.Name() == "str_val" {
					strRef = node
					found = true
					return false
				}
			}
			return true
		})
		if found {
			break
		}
	}
	if strRef.a == nil {
		t.Fatalf("failed to recover str_val AST reference")
	}
	if err := s.AssertSMTLIB2String(script); err != nil {
		t.Fatalf("AssertSMTLIB2String error: %v", err)
	}
	res, err := s.Check()
	if err != nil {
		t.Fatalf("solver check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
	m := s.Model()
	if m == nil {
		t.Fatalf("expected model from solver")
	}
	defer m.Close()

	strVal := m.Eval(strRef, true)
	if strVal.a == nil {
		t.Fatalf("model evaluation for str_val returned nil")
	}
	if !strVal.IsApp() {
		t.Fatalf("expected str_val model value to be application, got %s", strVal.String())
	}
	if name := strVal.Decl().Name(); name != "Atom" {
		t.Fatalf("expected outer constructor Atom, got %s", name)
	}
	if strVal.NumChildren() != 1 {
		t.Fatalf("Atom constructor should have 1 child, got %d", strVal.NumChildren())
	}
	atomField := strVal.Child(0)
	if !atomField.IsApp() {
		t.Fatalf("expected atom field to be constructor application, got %s", atomField.String())
	}
	if atomField.Decl().Name() != "OString" {
		t.Fatalf("expected atom field to be OString, got %s", atomField.Decl().Name())
	}
	if atomField.NumChildren() != 1 {
		t.Fatalf("OString should have one child, got %d", atomField.NumChildren())
	}
	stringLit := atomField.Child(0)
	val, ok := stringLit.AsStringLiteral()
	if !ok {
		t.Fatalf("expected to decode string literal from %s", stringLit.String())
	}
	if val != "hello world" {
		t.Fatalf("expected string literal 'hello world', got %q", val)
	}
}

func TestASTModelArraySelectFromDatatype(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	const script = `
(declare-datatypes ()
  ((OAtom
    (OString (str String))
    (ONumber (num Int))
    (OBoolean (bool Bool))
    ONull
    OUndef))
)

(declare-datatypes (T)
  ((OGenType
    (Atom (atom OAtom))
    (OObj (obj (Array String T)))
    (OArray (arr (Array Int T)))))
)

(declare-datatypes ()
  ((OGenTypeAtom (Atom (atom OAtom))))
)

(define-sort OTypeD0 () (OGenType OGenTypeAtom))

(declare-fun x () OTypeD0)
(assert (is-OString (atom (select (obj x) "a"))))
`

	asts, err := ctx.ParseSMTLIB2String(script)
	if err != nil {
		t.Fatalf("ParseSMTLIB2String error: %v", err)
	}
	var (
		xRef      AST
		selectRef AST
	)
	for _, root := range asts {
		root.Walk(func(node AST) bool {
			if !node.IsApp() {
				return true
			}
			decl := node.Decl()
			switch decl.Name() {
			case "x":
				if node.NumChildren() == 0 && xRef.a == nil {
					xRef = node
				}
			case "select", "Select":
				if selectRef.a == nil {
					selectRef = node
				}
			}
			return xRef.a == nil || selectRef.a == nil
		})
		if xRef.a != nil && selectRef.a != nil {
			break
		}
	}
	if xRef.a == nil {
		t.Fatalf("failed to locate AST for x")
	}
	if selectRef.a == nil {
		t.Fatalf("failed to locate select(obj x \"a\") AST")
	}

	s := ctx.NewSolver()
	defer s.Close()
	if err := s.AssertSMTLIB2String(script); err != nil {
		t.Fatalf("AssertSMTLIB2String error: %v", err)
	}
	res, err := s.Check()
	if err != nil {
		t.Fatalf("solver check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
	m := s.Model()
	if m == nil {
		t.Fatalf("expected model from solver")
	}
	defer m.Close()

	xVal := m.Eval(xRef, true)
	if xVal.a == nil {
		t.Fatalf("model evaluation for x returned nil")
	}
	if !xVal.IsApp() {
		t.Fatalf("expected x value to be application, got %s", xVal.String())
	}

	selected := m.Eval(selectRef, true)
	if selected.a == nil {
		t.Fatalf("model evaluation for select(obj x \"a\") returned nil")
	}
	if !selected.IsApp() || selected.Decl().Name() != "Atom" {
		t.Fatalf("expected select result to be Atom constructor, got %s", selected.String())
	}
	if selected.NumChildren() != 1 {
		t.Fatalf("Atom constructor should have one child, got %d", selected.NumChildren())
	}
	atom := selected.Child(0)
	if !atom.IsApp() || atom.Decl().Name() != "OString" {
		t.Fatalf("expected atom accessor to be OString, got %s", atom.String())
	}
	if atom.NumChildren() != 1 {
		t.Fatalf("OString should expose 1 child, got %d", atom.NumChildren())
	}
	if _, ok := atom.Child(0).AsStringLiteral(); !ok {
		t.Fatalf("expected to read string literal from selected entry")
	}
}
