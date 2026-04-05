import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_eq_univ : a • s = univ ↔ s = univ := by
  rw [smul_eq_iff_eq_inv_smul, Set.smul_set_univ]

