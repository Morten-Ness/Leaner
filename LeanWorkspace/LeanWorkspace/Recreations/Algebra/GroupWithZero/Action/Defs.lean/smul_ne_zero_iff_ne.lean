import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [Group α] [AddMonoid β] [DistribMulAction α β]

theorem smul_ne_zero_iff_ne (a : α) {x : β} : a • x ≠ 0 ↔ x ≠ 0 := not_congr <| smul_eq_zero_iff_eq a

