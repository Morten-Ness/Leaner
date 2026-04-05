import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem card_inv (s : Finset α) : #s⁻¹ = #s := card_image_of_injective _ inv_injective

