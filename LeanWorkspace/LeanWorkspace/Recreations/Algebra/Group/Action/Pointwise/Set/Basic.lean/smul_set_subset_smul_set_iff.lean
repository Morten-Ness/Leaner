import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_set_subset_smul_set_iff : a • A ⊆ a • B ↔ A ⊆ B := image_subset_image_iff <| MulAction.injective _

