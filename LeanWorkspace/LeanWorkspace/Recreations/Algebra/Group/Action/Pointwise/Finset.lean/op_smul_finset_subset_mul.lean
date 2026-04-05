import Mathlib

open scoped Pointwise RightActions

variable {F α β γ : Type*}

variable [Mul α] [DecidableEq α] {s t u : Finset α} {a : α}

theorem op_smul_finset_subset_mul : a ∈ t → op a • s ⊆ s * t := image_subset_image₂_left

