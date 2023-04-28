import Mathlib.Algebra.GroupWithZero.Basic 

section CancelMonoidWithZero
variable {M₀ : Type _} [CancelMonoidWithZero M₀] {a b : M₀}

theorem mul_right_eq_self₀' : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff

end CancelMonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀] {a : G₀}

theorem inv_mul_cancel_rw (h : a ≠ 0) : a⁻¹ * a = 1 := by 
    rw [← mul_inv_cancel_right₀ (inv_ne_zero h) (a⁻¹ * a)]
    --rw [mul_assoc]
    rw [mul_inv_cancel_right₀ h]
    rw [mul_inv_cancel (inv_ne_zero h)]

theorem inv_mul_cancel' (h : a ≠ 0) : a⁻¹ * a = 1 := by
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h, mul_inv_cancel_right₀ h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    --_ = 1 := by simp[inv_ne_zero h, mul_inv_cancel]-- not sure why this doesn't work
    _ = 1 := by simp only [ne_eq, inv_ne_zero h, not_false_eq_true, mul_inv_cancel] 

theorem inv_mul_cancel_simp_only (h : a ≠ 0) : a⁻¹ * a = 1 := by
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp only [ne_eq, inv_ne_zero h, not_false_eq_true, mul_inv_cancel_right₀]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp only [ne_eq, h, not_false_eq_true, mul_inv_cancel_right₀]
    _ = 1 := by simp only [ne_eq, inv_ne_zero h, not_false_eq_true, mul_inv_cancel]

theorem inv_mul_cancel_vision (h : a ≠ 0) : a⁻¹ * a = 1 := by
  calc'
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ 
            = a⁻¹ * a⁻¹⁻¹
            = 1
    using [ne_eq, inv_ne_zero h, not_false_eq_true, mul_inv_cancel_right₀, mul_inv_cancel]
    -- could maybe be inferred from tags?

end GroupWithZero 