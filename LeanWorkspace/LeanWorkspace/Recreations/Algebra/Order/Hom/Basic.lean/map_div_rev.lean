import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupSeminormClass F α β] (f : F) (x y : α)

theorem map_div_rev : f (x / y) = f (y / x) := by rw [← inv_div, map_inv_eq_map]

