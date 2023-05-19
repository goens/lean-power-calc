import PowerCalc.Language


def binomial4 := [expr| (x + y)^4]
def binomial4_step1 := [expr| (x + y)^2 * (x + y)^2]
def binomial4_step2 := [expr| ((x^2) + (2*x*y) + (y^2)) * ((x^2) + (2*x*y) + (y^2))]
def binomial4_expanded := [expr| (x^4) + (4*(x^3)*y) + (6*(x^2)*(y^2)) + (4*x*(y^3)) + (y^4)]


def sdiff_rw_rule1 := [expr| a ⊔ b ⊓ c ≈ (a ⊔ b) ⊓ (a ⊔ c)]
def sdiff_rw_rule2 := [expr| a ⊓ (b ⊔ c) ≈ a ⊓ b ⊔ a ⊓ c]
def sdiff_rw_rule3 := [expr| a ⊓ b ⊔ a \ b ≈ a]
def sdiff_rw_rule4 := [expr| a ⊔ a ⊓ b ≈ a]
def sdiff_rw_rule5 := [expr| a ⊓ a ≈ a]

def sdiff_sup1_step0 := [expr| y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z]
def sdiff_sup1_step1 := [expr| (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ y \ z) ]
def sdiff_sup1_step2 := [expr| (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z)]
def sdiff_sup1_step3 := [expr| (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) ]
def sdiff_sup1_step4 := [expr| (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y)]
def sdiff_sup1_step5 := [expr| (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x)]
def sdiff_sup1_step6 := [expr| y ]

def polynomials := [binomial4,  binomial4_step1, binomial4_step2, binomial4_expanded]
def sdiff_rewrites := [sdiff_rw_rule1, sdiff_rw_rule2, sdiff_rw_rule3, sdiff_rw_rule4, sdiff_rw_rule5]
def sdiff_sup1_steps := [sdiff_sup1_step0, sdiff_sup1_step1, sdiff_sup1_step2, sdiff_sup1_step3, sdiff_sup1_step4, sdiff_sup1_step5, sdiff_sup1_step6]
def main : IO Unit := do
  let polynomial_strings := polynomials.map (·.toSexp.toString)
  IO.println ("\n".intercalate polynomial_strings)

  let sdiff_rewrites_strings := sdiff_rewrites.map (·.toSexp.toString)
  IO.println ("\n".intercalate sdiff_rewrites_strings)

  let sdiff_sup1_steps_strings := sdiff_sup1_steps.map (·.toSexp.toString)
  IO.println ("\n".intercalate sdiff_sup1_steps_strings)
