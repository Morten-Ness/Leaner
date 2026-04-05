import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem inv_insert (a : α) (s : Finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := image_insert _ _ _

