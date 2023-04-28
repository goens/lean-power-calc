import Lean
inductive Expr
  | Var : String → Expr
  | Add : Expr → Expr → Expr
  | Sub : Expr → Expr → Expr
  | Mul : Expr → Expr → Expr
  | Pow : Expr → Expr → Expr
  | Const : Int → Expr
  deriving DecidableEq, Inhabited, Repr

inductive Sexp
  | atom : String → Sexp
  | list : List Sexp → Sexp
  deriving Inhabited, Repr

def Expr.toSexp : Expr → Sexp
  | Expr.Var x => Sexp.atom x
  | Expr.Add e₁ e₂ => Sexp.list [Sexp.atom "+", e₁.toSexp, e₂.toSexp]
  | Expr.Sub e₁ e₂ => Sexp.list [Sexp.atom "-", e₁.toSexp, e₂.toSexp]
  | Expr.Mul e₁ e₂ => Sexp.list [Sexp.atom "*", e₁.toSexp, e₂.toSexp]
  | Expr.Pow e₁ e₂ => Sexp.list [Sexp.atom "pow", e₁.toSexp, e₂.toSexp]
  | Expr.Const n => Sexp.atom (toString n)


partial def Sexp.toString : Sexp → String
  | Sexp.atom s => s
  | Sexp.list l => "(" ++ String.intercalate " " (l.map Sexp.toString) ++ ")"

declare_syntax_cat expr
syntax ident : expr
syntax num : expr
syntax:65 expr "+" expr : expr
syntax:65 expr "-" expr : expr
syntax:70 expr "*" expr : expr
syntax:75 expr "^" expr : expr
syntax "(" expr ")" : expr
syntax "[expr|" expr "]" : term

macro_rules
 | `([expr| $id:ident ]) => `(Expr.Var $(Lean.quote id.getId.toString))
 | `([expr| $n:num ]) => `(Expr.Const $(Lean.quote n.getNat))
 | `([expr| $e₁ + $e₂ ]) => `(Expr.Add [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ - $e₂ ]) => `(Expr.Sub [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ * $e₂ ]) => `(Expr.Mul [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ ^ $e₂ ]) => `(Expr.Pow [expr| $e₁] [expr| $e₂])
 | `([expr| ($e) ]) => `([expr| $e ])


#eval [expr| x^4 + 1].toSexp.toString
#eval [expr| (x^4) + 1].toSexp.toString
#eval [expr| x^(4 + 1)].toSexp.toString
set_option pp.all true
#check `(expr| x^4 + 1)
