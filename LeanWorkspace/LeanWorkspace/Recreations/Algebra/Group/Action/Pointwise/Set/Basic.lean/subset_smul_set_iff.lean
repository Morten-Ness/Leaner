import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem subset_smul_set_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B := by
  refine (image_subset_iff.trans ?_).symm; congr! 1;
  exact ((MulAction.toPerm _).image_eq_preimage_symm _).symm

