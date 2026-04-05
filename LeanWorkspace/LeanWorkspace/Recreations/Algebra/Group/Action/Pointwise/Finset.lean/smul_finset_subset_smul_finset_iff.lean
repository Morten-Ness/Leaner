import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem smul_finset_subset_smul_finset_iff : a • s ⊆ a • t ↔ s ⊆ t := image_subset_image_iff <| MulAction.injective _

