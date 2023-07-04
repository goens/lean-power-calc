import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

theorem square_eq_two_times [CommRing R] (x : R) :
x^2 = x * x := by calc 
x^2 = Monoid.npow (Nat.succ (Nat.succ 0)) x := 
  by simp [HPow.hPow, instHPow]
  _ = x * (x * 1) := 
  by rw [Monoid.npow_succ, Monoid.npow_succ, Monoid.npow_zero]
  _ = x * x := by rw [Monoid.mul_one]

theorem double_eq_two_additions [CommRing R] (x : R) :
   2*x = x + x := by ring

theorem binomial_formula [CommRing R] (x y : R) : 
(x + y)^2 = x^2 + 2*(x*y) + y ^2 := by calc 
(x + y)^2 = (x + y)*(x + y) := by rw [square_eq_two_times]
        _ = x*x + y*x + (x*y + y*y) := by rw [Distrib.left_distrib,
                      Distrib.right_distrib, Distrib.right_distrib]
        _ = x*x + x*y + x*y + y*y := by simp only [add_left_comm,
                      add_assoc, mul_comm]
        _ = x*x + (x*y + x*y) + y*y := by simp only [add_assoc]
        _ = x*x + 2*(x*y) + y*y := by rw [← double_eq_two_additions]
        _ = x^2 + 2*(x*y) + y^2 := by rw [square_eq_two_times,
                       square_eq_two_times]


theorem binomial_formula' [CommRing R] (x y : R) : 
  (x + y)^2 = x^2 + 2*x*y + y ^2 := by ring


theorem trinomial [CommRing R] (x y z : R) : 
  (x + y + z)^3 = x * y * z * 6 + x * y ^ 2 * 3 + 
    x * z ^ 2 * 3 + x ^ 2 * y * 3 + x ^ 2 * z * 3 + 
    x ^ 3 + y * z ^ 2 * 3 + y ^ 2 * z * 3 + y ^ 3 + z ^ 3 := by ring
          