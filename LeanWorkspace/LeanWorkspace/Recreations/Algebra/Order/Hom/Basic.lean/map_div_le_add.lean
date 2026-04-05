import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupSeminormClass F α β] (f : F) (x y : α)

theorem map_div_le_add : f (x / y) ≤ f x + f y := by
  rw [div_eq_mul_inv, ← map_inv_eq_map f y]
  exact map_mul_le_add _ _ _

