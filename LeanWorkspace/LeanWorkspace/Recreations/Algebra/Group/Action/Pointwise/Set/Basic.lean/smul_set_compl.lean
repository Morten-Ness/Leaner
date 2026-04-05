import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_compl : a • sᶜ = (a • s)ᶜ := by
  simp_rw [Set.compl_eq_univ_diff, Set.smul_set_sdiff, Set.smul_set_univ]

