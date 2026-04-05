import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem inv_subset_inv (h : s ⊆ t) : s⁻¹ ⊆ t⁻¹ := image_subset_image h

