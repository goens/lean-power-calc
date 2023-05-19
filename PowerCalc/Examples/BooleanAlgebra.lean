import Mathlib.Order.BooleanAlgebra
import EggTactic


variable {α : Type u} {β : Type _} {w x y z : α}
variable [instGenBoolAlg : GeneralizedBooleanAlgebra α]

theorem sdiff_le' : x \ y ≤ x :=
  calc
    x \ y ≤ x ⊓ y ⊔ x \ y := le_sup_right
    _ = x := sup_inf_sdiff x y

/-
theorem sdiff_le_vision : x \ y ≤ x :=
  calc'
    x \ y ≤ x ⊓ y ⊔ x \ y 
          = x 
    using [le_sup_right, sup_inf_sdiff]
-/

theorem sdiff_sup' : y \ (x ⊔ z) = y \ x ⊓ y \ z :=
  sdiff_unique
    (calc
      y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ y \ z) :=
          by rw [sup_inf_left]
      _ = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by rw [@inf_sup_left _ _ y]
      _ = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) := by ac_rfl
      _ = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y) := by rw [sup_inf_sdiff, sup_inf_sdiff]
      _ = (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x) := by ac_rfl
      _ = y := by rw [sup_inf_self, sup_inf_self, inf_idem])
    (calc
      y ⊓ (x ⊔ z) ⊓ (y \ x ⊓ y \ z) = (y ⊓ x ⊔ y ⊓ z) ⊓ (y \ x ⊓ y \ z) := by rw [inf_sup_left]
      _ = y ⊓ x ⊓ (y \ x ⊓ y \ z) ⊔ y ⊓ z ⊓ (y \ x ⊓ y \ z) := by rw [inf_sup_right]
      _ = y ⊓ x ⊓ y \ x ⊓ y \ z ⊔ y \ x ⊓ (y \ z ⊓ (y ⊓ z)) := by ac_rfl
      _ = ⊥ := by rw [inf_inf_sdiff, bot_inf_eq, bot_sup_eq, @inf_comm _ _ (y \ z),
                      inf_inf_sdiff, inf_bot_eq])

set_option trace.EggTactic.egg true
theorem sdiff_sup_egg : y \ (x ⊔ z) = y \ x ⊓ y \ z :=
  sdiff_unique
      (by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        eggxplosion [rw1, rw2, rw3, rw4, rw5] simplify)
      (by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        eggxplosion [rw1, rw2, rw3, rw4, rw5] simplify)


theorem sdiff_sup_egg1 :
  y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ y \ z) := by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        eggxplosion [rw1, rw2, rw3, rw4, rw5] simplify noInstantiation
        done


theorem sdiff_sup_egg2 :
  (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ y \ z) = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        eggxplosion [rw1, rw2, rw3, rw4, rw5] simplify

theorem sdiff_sup_egg3 :
  (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z)) = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z) := by
        have rw1 : forall a b c : α,  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := fun a b c => @sup_inf_left _ _ a b c
        have rw2 : forall a b c : α, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := fun a b c => @inf_sup_left _ _ a b c
        have rw3 : forall a b : α, a ⊓ b ⊔ a \ b = a := fun a b => @sup_inf_sdiff _ _ a b
        have rw4 : forall a b : α, a ⊔ a ⊓ b = a := fun a b => @sup_inf_self _ _ a b
        have rw5 : forall a : α, a ⊓ a = a := fun a => @inf_idem _ _ a
        eggxplosion [rw1, rw2, rw3, rw4, rw5] simplify


theorem sdiff_sup_vision : y \ (x ⊔ z) = y \ x ⊓ y \ z :=
  sdiff_unique
    (calc'
      y ⊓ (x ⊔ z) ⊔ y \ x ⊓ y \ z = (y ⊓ (x ⊔ z) ⊔ y \ x) ⊓ (y ⊓ (x ⊔ z) ⊔ y \ z)
                                 -- = (y ⊓ x ⊔ y ⊓ z ⊔ y \ x) ⊓ (y ⊓ x ⊔ y ⊓ z ⊔ y \ z)
                                  = (y ⊓ z ⊔ (y ⊓ x ⊔ y \ x)) ⊓ (y ⊓ x ⊔ (y ⊓ z ⊔ y \ z))
                                 -- = (y ⊓ z ⊔ y) ⊓ (y ⊓ x ⊔ y)
                                  = (y ⊔ y ⊓ z) ⊓ (y ⊔ y ⊓ x)
                                  = y 
      using [sup_inf_left, inf_sup_left, ac_rfl, sup_inf_sdiff, sup_inf_self, inf_idem]
    (calc'
      y ⊓ (x ⊔ z) ⊓ (y \ x ⊓ y \ z) = (y ⊓ x ⊔ y ⊓ z) ⊓ (y \ x ⊓ y \ z) 
                                    = y ⊓ x ⊓ (y \ x ⊓ y \ z) ⊔ y ⊓ z ⊓ (y \ x ⊓ y \ z)
                                    = y ⊓ x ⊓ y \ x ⊓ y \ z ⊔ y \ x ⊓ (y \ z ⊓ (y ⊓ z))
                                    = ⊥
      using [inf_inf_sdiff, bot_inf_eq, bot_sup_eq, inf_comm, inf_bot_eq, inf_sup_left, inf_sup_right, ac_rfl]
