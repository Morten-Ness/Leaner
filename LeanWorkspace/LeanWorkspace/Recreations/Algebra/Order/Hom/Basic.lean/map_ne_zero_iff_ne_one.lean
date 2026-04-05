import Mathlib

variable {ι F α β γ δ : Type*}

variable [FunLike F α β]

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupNormClass F α β] (f : F) {x : α}

theorem map_ne_zero_iff_ne_one : f x ≠ 0 ↔ x ≠ 1 := (map_eq_zero_iff_eq_one _).not

