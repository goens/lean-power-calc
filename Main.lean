import PowerCalc.Language


def binomial4 := [expr| (x + y)^4]
def binomial4_step1 := [expr| (x + y)^2 * (x + y)^2]
def binomial4_step2 := [expr| ((x^2) + (2*x*y) + (y^2)) * ((x^2) + (2*x*y) + (y^2))]
def binomial4_expanded := [expr| (x^4) + (4*(x^3)*y) + (6*(x^2)*(y^2)) + (4*x*(y^3)) + (y^4)]


def polynomials := [binomial4,  binomial4_step1, binomial4_step2, binomial4_expanded]
def main : IO Unit :=
  let polynomial_strings := polynomials.map (·.toSexp.toString)
  IO.println ("\n".intercalate polynomial_strings)
