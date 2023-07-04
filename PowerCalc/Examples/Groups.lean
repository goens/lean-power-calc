import Mathlib.Algebra.Group.Defs

theorem inverse_involution [Group G] (g : G) : g⁻¹⁻¹ = g := by
  calc
    g⁻¹⁻¹ = g⁻¹⁻¹ * 1 := by rw [mul_one]
        _ = g⁻¹⁻¹ * (g⁻¹ * g) := by rw [inv_mul_self]
        _ = (g⁻¹⁻¹ * g⁻¹) * g := by rw [mul_assoc]
        _ = 1 * g := by rw [inv_mul_self]
        _ = g := by rw [one_mul]

theorem inverse_involution' [Group G] (g : G) : g⁻¹⁻¹ = g := by
  rw [←  mul_one g⁻¹⁻¹, ←  inv_mul_self g,
      ← mul_assoc, inv_mul_self g⁻¹,  one_mul]
