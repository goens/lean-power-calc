import Lean
inductive Expr
  | var : String → Expr
  | binaryRel : String → Expr → Expr → Expr
  | const : Int → Expr
  deriving DecidableEq, Inhabited, Repr

inductive Sexp
  | atom : String → Sexp
  | list : List Sexp → Sexp
  deriving Inhabited, Repr

def Expr.toSexp : Expr → Sexp
  | Expr.var x => Sexp.atom x
  | Expr.binaryRel op e₁ e₂ => Sexp.list [Sexp.atom op, e₁.toSexp, e₂.toSexp]
  | Expr.const n => Sexp.atom (toString n)


partial def Sexp.toString : Sexp → String
  | Sexp.atom s => s
  | Sexp.list l => "(" ++ String.intercalate " " (l.map Sexp.toString) ++ ")"

declare_syntax_cat expr
syntax ident : expr
syntax "⊥" : expr
syntax num : expr
syntax:65 expr "+" expr : expr
syntax:65 expr "-" expr : expr
syntax:70 expr "*" expr : expr
syntax:75 expr "^" expr : expr
syntax:76 expr "\\" expr : expr
syntax:80 expr "⊔" expr : expr
syntax:80 expr "⊓" expr : expr
syntax:100 expr "≈" expr : expr
syntax "(" expr ")" : expr
syntax "[expr|" expr "]" : term

macro_rules
 | `([expr| $id:ident ]) => `(Expr.var $(Lean.quote id.getId.toString))
 | `([expr| $n:num ]) => `(Expr.const $(Lean.quote n.getNat))
 | `([expr| ⊥ ]) => `(Expr.const 0)
 | `([expr| $e₁ + $e₂ ]) => `(Expr.binaryRel "+" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ - $e₂ ]) => `(Expr.binaryRel "-" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ * $e₂ ]) => `(Expr.binaryRel "*" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ ^ $e₂ ]) => `(Expr.binaryRel "pow" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ ⊔ $e₂ ]) => `(Expr.binaryRel "sqcup" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ ⊓ $e₂ ]) => `(Expr.binaryRel "sqcap" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ \ $e₂ ]) => `(Expr.binaryRel "setminus" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ ≈ $e₂ ]) => `(Expr.binaryRel "eq" [expr| $e₁] [expr| $e₂])
 | `([expr| ($e) ]) => `([expr| $e ])


#eval [expr| x^4 + 1].toSexp.toString
#eval [expr| (x^4) + 1].toSexp.toString
#eval [expr| x^(4 + 1)].toSexp.toString
set_option pp.all true
#check `(expr| x^4 + 1)
