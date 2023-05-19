import Lean
inductive Expr
  | var : String → Expr
  | mvar : String → Expr
  | binaryRel : String → Expr → Expr → Expr
  | const : Int → Expr
  deriving DecidableEq, Inhabited, Repr

inductive Sexp
  | atom : String → Sexp
  | list : List Sexp → Sexp
  deriving Inhabited, Repr

def Expr.toSexp : Expr → Sexp
  | Expr.var x => Sexp.atom x
  | Expr.mvar x => Sexp.atom ("?" ++ x)
  | Expr.binaryRel op e₁ e₂ => Sexp.list [Sexp.atom op, e₁.toSexp, e₂.toSexp]
  | Expr.const n => Sexp.atom (toString n)

structure Rewrite where
  (lhs : Expr)
  (rhs : Expr)

partial def Sexp.toString : Sexp → String
  | Sexp.atom s => s
  | Sexp.list l => "(" ++ String.intercalate " " (l.map Sexp.toString) ++ ")"

def Rewrite.toString (rw : Rewrite) : String :=
  let (lhs_raw,rhs_raw) := (rw.lhs.toSexp.toString, rw.rhs.toSexp.toString)
  let lhs := if lhs_raw.data[0]? = some '(' then lhs_raw else s!"({lhs_raw})"
  let rhs := if rhs_raw.data[0]? = some '(' then rhs_raw else s!"({rhs_raw})"
  s!"\"{lhs}\" => \"{rhs}\""

def Rewrite.toRWString (rw : Rewrite) (name := "rewrite") : String :=
  s!"rw!(\"{name}\"; {rw.toString})"

def Rewrite.toTestString (rw : Rewrite) (name := "rewrite") : String :=
  s!"egg::test_fn! \{\n" ++
s!"  {name}, rules(),\n" ++
"  runner = Runner::default()\n" ++
"      .with_time_limit(std::time::Duration::from_secs(30))\n" ++
"      .with_iter_limit(120)\n" ++
"      .with_node_limit(200_000),\n" ++
s!"    {rw.toString} }"

declare_syntax_cat expr
syntax ident : expr
syntax "?" ident : expr
syntax "⊥" : expr
syntax num : expr
syntax:65 expr "+" expr : expr
syntax:65 expr "-" expr : expr
syntax:70 expr "*" expr : expr
syntax:75 expr "^" expr : expr
syntax:76 expr "\\" expr : expr
syntax:80 expr "⊔" expr : expr
syntax:80 expr "⊓" expr : expr
syntax "(" expr ")" : expr
syntax "[expr|" expr "]" : term
syntax "[rw|" expr "=>" expr "]" : term

macro_rules
 | `([expr| $id:ident ]) => `(Expr.var $(Lean.quote id.getId.toString))
 | `([expr| ?$id:ident ]) => `(Expr.mvar $(Lean.quote id.getId.toString))
 | `([expr| $n:num ]) => `(Expr.const $(Lean.quote n.getNat))
 | `([expr| ⊥ ]) => `(Expr.const 0)
 | `([expr| $e₁ + $e₂ ]) => `(Expr.binaryRel "+" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ - $e₂ ]) => `(Expr.binaryRel "-" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ * $e₂ ]) => `(Expr.binaryRel "*" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ ^ $e₂ ]) => `(Expr.binaryRel "pow" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ ⊔ $e₂ ]) => `(Expr.binaryRel "sqcup" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ ⊓ $e₂ ]) => `(Expr.binaryRel "sqcap" [expr| $e₁] [expr| $e₂])
 | `([expr| $e₁ \ $e₂ ]) => `(Expr.binaryRel "setminus" [expr| $e₁] [expr| $e₂])
 | `([expr| ($e) ]) => `([expr| $e ])
 | `([rw| $e₁ => $e₂]) => `(Rewrite.mk [expr| $e₁ ] [expr| $e₂])


#eval [expr| x^4 + 1].toSexp.toString
#eval [expr| (x^4) + 1].toSexp.toString
#eval [expr| x^(4 + 1)].toSexp.toString
set_option pp.all true
#check `(expr| x^4 + 1)

