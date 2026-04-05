import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem closure_eq_image_prod (s : Set M) :
    (closure s : Set M) = List.prod '' { l : List M | ∀ x ∈ l, x ∈ s } := by
  rw [Submonoid.closure_eq_mrange, coe_mrange, ← Set.range_list_map_coe, ← Set.range_comp]
  exact congrArg _ (funext <| FreeMonoid.lift_apply _)

