import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
-- based on Mathlib.Data.Nat.Choose.Central
namespace Nat

def centralBinom (n : ℕ) :=
  (2 * n).choose n

theorem centralBinom_eq_two_mul_choose (n : ℕ) : centralBinom n = (2 * n).choose n :=
  rfl

theorem centralBinom_pos (n : ℕ) : 0 < centralBinom n :=
  choose_pos (Nat.le_mul_of_pos_left zero_lt_two)

theorem centralBinom_ne_zero (n : ℕ) : centralBinom n ≠ 0 :=
  (centralBinom_pos n).ne'

@[simp]
theorem centralBinom_zero : centralBinom 0 = 1 :=
  choose_zero_right _

/-- The central binomial coefficient is the largest binomial coefficient.
-/
theorem choose_le_centralBinom (r n : ℕ) : choose (2 * n) r ≤ centralBinom n :=
  calc
    (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) := choose_le_middle r (2 * n)
    _ = (2 * n).choose n := by rw [Nat.mul_div_cancel_left n zero_lt_two]

theorem two_le_centralBinom (n : ℕ) (n_pos : 0 < n) : 2 ≤ centralBinom n :=
  calc
    2 ≤ 2 * n := le_mul_of_pos_right n_pos
    _ = (2 * n).choose 1 := (choose_one_right (2 * n)).symm
    _ ≤ centralBinom n := choose_le_centralBinom 1 n

/-- An inductive property of the central binomial coefficient.
-/
theorem succ_mul_centralBinom_succ_rw (n : ℕ) :
    (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n := by
    unfold centralBinom
    rw [mul_comm]
    --
    --rw [choose_succ_right_eq (2 * (n + 1)) n, choose_mul_succ_eq]
    rw [mul_add 2 n 1]; simp
    rw [choose_succ_right_eq] 
    rw [choose_mul_succ_eq]
    --rw [choose_succ_right_eq (2 * (n + 1)) n]
    -- TODO: finish
    --_ = 2 * ((2 * n + 1).choose n * (n + 1)) := by ring
    rw [two_mul n, add_assoc, Nat.add_sub_cancel_left]
    rw [choose_mul_succ_eq]
    rw [mul_assoc, mul_comm (2 * n + 1)]



theorem succ_mul_centralBinom_succ (n : ℕ) :
    (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n :=
  calc
    (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) := mul_comm _ _
    _ = (2 * n + 1).choose n * (2 * n + 2) := by rw [choose_succ_right_eq, choose_mul_succ_eq]
    _ = 2 * ((2 * n + 1).choose n * (n + 1)) := by ring
    _ = 2 * ((2 * n + 1).choose n * (2 * n + 1 - n)) := by rw [two_mul n, add_assoc,
                                                               Nat.add_sub_cancel_left]
    _ = 2 * ((2 * n).choose n * (2 * n + 1)) := by rw [choose_mul_succ_eq]
    _ = 2 * (2 * n + 1) * (2 * n).choose n := by rw [mul_assoc, mul_comm (2 * n + 1)]

-- maybe leave some steps out
theorem succ_mul_centralBinom_succ_vision (n : ℕ) :
    (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n := by
  calc'
    (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1)
                                           = (2 * n + 1).choose n * (2 * n + 2)
                                           = 2 * ((2 * n + 1).choose n * (n + 1))
                                           = 2 * ((2 * n + 1).choose n * (2 * n + 1 - n))
                                           = 2 * ((2 * n).choose n * (2 * n + 1)) 
                                           = 2 * (2 * n + 1) * (2 * n).choose n 
-- these could be annotated with e.g. @[calc] tags, or @[simp] or just gathered from the background somehow clever
using [choose_succ_right_eq, choose_mul_succ_eq, ring, two_mul n, add_assoc,
       mul_assoc, mul_comm, Nat.add_sub_cancel_left, choose_mul_succ_eq]