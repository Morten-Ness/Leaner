import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ := mem_image_of_mem _ ha

