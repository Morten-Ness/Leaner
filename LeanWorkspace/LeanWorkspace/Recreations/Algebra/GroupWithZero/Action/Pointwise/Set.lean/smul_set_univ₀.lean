import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

theorem smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ := image_univ_of_surjective <| MulAction.surjective₀ ha

