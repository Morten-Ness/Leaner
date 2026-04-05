import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_subset_iff_subset_inv_smul_set : a • A ⊆ B ↔ A ⊆ a⁻¹ • B := by
  refine image_subset_iff.trans ?_
  congr! 1
  exact ((MulAction.toPerm _).image_symm_eq_preimage _).symm

