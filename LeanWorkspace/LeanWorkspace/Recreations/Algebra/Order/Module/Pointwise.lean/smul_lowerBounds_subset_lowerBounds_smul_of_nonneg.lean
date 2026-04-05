import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [SMul α β] [Preorder α] [Preorder β] [Zero α] [PosSMulMono α β] {a : α} {s : Set β}

theorem smul_lowerBounds_subset_lowerBounds_smul_of_nonneg (ha : 0 ≤ a) :
    a • lowerBounds s ⊆ lowerBounds (a • s) := (monotone_smul_left_of_nonneg ha).image_lowerBounds_subset_lowerBounds_image

