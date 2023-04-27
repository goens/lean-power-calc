import Mathlib.Analysis.Convex.Function

variable {𝕜 E F α β ι : Type _}
variable [OrderedSemiring 𝕜]
variable [AddCommMonoid E] [AddCommMonoid F]
variable [OrderedAddCommMonoid α] [OrderedAddCommMonoid β]
variable [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}
 
theorem ConvexOn.add' (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g) := by
constructor
exact hf.1
intro x hx y hy a b ha hb hab
calc
  f (a • x + b • y) + g (a • x + b • y) ≤ a • f x + b • f y + (a • g x + b • g y) :=
    add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
  _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]

variable [SMul 𝕜 E] [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β}
theorem ConvexOn.convex_le' (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) := by
  intro x hx y hy a b ha hb hab
  constructor
  {exact hf.1 hx.1 hy.1 ha hb hab}
  {calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha hb hab
    _ ≤ a • r + b • r :=
      (add_le_add (smul_le_smul_of_nonneg hx.2 ha) (smul_le_smul_of_nonneg hy.2 hb))
    _ = r := Convex.combo_self hab r
  }

  -- many more in Mathlib.Analysis.Convex.Function ...