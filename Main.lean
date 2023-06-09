import PowerCalc.Language


def binomial4 := [expr| (x + y)^4]
def binomial4_step1 := [expr| (x + y)^2 * (x + y)^2]
def binomial4_step2 := [expr| ((x^2) + (2*x*y) + (y^2)) * ((x^2) + (2*x*y) + (y^2))]
def binomial4_expanded := [expr| (x^4) + (4*(x^3)*y) + (6*(x^2)*(y^2)) + (4*x*(y^3)) + (y^4)]


def sup_inf_left := [rw| ?x ⊔ (?y ⊓ ?z) => (?x ⊔ ?y) ⊓ (?x ⊔ ?z)]
def inf_sup_left := [rw| ?x ⊓ (?y ⊔ ?z) => (?x ⊓ ?y) ⊔ (?x ⊓ ?z)]
def sup_inf_sdiff := [rw| (?x ⊓ ?y) ⊔ (?x \ ?y) => ?x]
def sup_inf_self := [rw| ?a ⊔ (?a ⊓ ?b) => ?a]
def inf_idem := [rw| ?a ⊓ ?a => ?a]
def sup_assoc := [rw| ?a ⊓ (?b ⊓ ?c) => (?a ⊓ ?b) ⊓ ?c]
def inf_assoc := [rw| ?a ⊔ (?b ⊔ ?c) => (?a ⊔ ?b) ⊔ ?c]
def sup_comm := [rw| ?a ⊔ ?b => ?b ⊔ ?a]
def inf_comm := [rw| ?a ⊓ ?b => ?b ⊓ ?a]
def sup_assoc' := [rw| (?a ⊓ ?b) ⊓ ?c => ?a ⊓ (?b ⊓ ?c) ]
def inf_assoc' := [rw| (?a ⊔ ?b) ⊔ ?c => ?a ⊔ (?b ⊔ ?c) ]
def sup_comm' := [rw| ?b ⊔ ?a => ?a ⊔ ?b ]
def inf_comm' := [rw| ?b ⊓ ?a => ?a ⊓ ?b ]

def sdiff_sup1_step0 := [expr| (y ⊓ (x ⊔ z)) ⊔ (y \ x) ⊓ (y \ z)]
def sdiff_sup1_step1 := [expr| (y ⊓ (x ⊔ z) ⊔ (y \ x)) ⊓ (y ⊓ (x ⊔ z) ⊔ (y \ z)) ]
def sdiff_sup1_step2 := [expr| (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z)]
def sdiff_sup1_step3 := [expr| (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) ]
def sdiff_sup1_step4 := [expr| (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y)]
def sdiff_sup1_step5 := [expr| (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x)]
def sdiff_sup1_step6 := [expr| y ]

def polynomials := [binomial4,  binomial4_step1, binomial4_step2, binomial4_expanded]
def sdiff_rewrites := [sup_inf_left, inf_sup_left, sup_inf_sdiff, sup_inf_self, inf_idem, sup_assoc, inf_assoc, sup_comm, inf_comm, sup_assoc', inf_assoc', sup_comm', inf_comm']
def sdiff_sup1_steps := [sdiff_sup1_step0, sdiff_sup1_step1, sdiff_sup1_step2, sdiff_sup1_step3, sdiff_sup1_step4, sdiff_sup1_step5, sdiff_sup1_step6]

def sdiff_sup1_main : Rewrite := { lhs := sdiff_sup1_step0, rhs := sdiff_sup1_step6 }
def sdiff_sup1_subgoals : List Rewrite :=
  let pairs := sdiff_sup1_steps.zip sdiff_sup1_steps.tail!
  pairs.map fun (lhs,rhs) => { lhs := lhs, rhs := rhs }

def main : IO Unit := do
  let polynomial_strings := polynomials.map (·.toSexp.toString)
  IO.println ("\n".intercalate polynomial_strings)

  let sdiff_rewrites_names := ["sup_inf_left", "inf_sup_left", "sup_inf_sdiff", "sup_inf_self", "inf_idem", "sup_assoc", "inf_assoc", "sup_comm", "inf_comm", "sup_assoc'", "inf_assoc'", "sup_comm'", "inf_comm'"]
  let sdiff_rewrites_strings := sdiff_rewrites.zip sdiff_rewrites_names |>.map fun (rw,n) => rw.toRWString n
  IO.println (",\n".intercalate sdiff_rewrites_strings)

  IO.println (sdiff_sup1_main.toTestString "sdiff_sup1")

  let sdiff_sup1_subgoal_names := List.range sdiff_sup1_subgoals.length |>.map fun n => s!"subgoal{n+1}"
  let sdiff_sup1_subgoal_strings := sdiff_sup1_subgoals.zip sdiff_sup1_subgoal_names |>.map fun (rw,n)  => rw.toTestString n
  IO.println ("\n".intercalate sdiff_sup1_subgoal_strings)

