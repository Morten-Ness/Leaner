import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹ := coe_image.trans Set.image_inv_eq_inv

