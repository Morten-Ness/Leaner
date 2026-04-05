import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupSeminormClass F α β] (f : F) (x y : α)

theorem le_map_add_map_div' : f x ≤ f y + f (y / x) := by
  simpa only [add_comm, map_div_rev, div_mul_cancel] using map_mul_le_add f (x / y) y

