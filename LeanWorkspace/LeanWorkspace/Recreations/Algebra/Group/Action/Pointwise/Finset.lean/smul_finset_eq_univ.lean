import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_eq_univ [Fintype β] : a • s = univ ↔ s = univ := by
  rw [smul_eq_iff_eq_inv_smul, Finset.smul_finset_univ]

