import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem image_inv_eq_inv : (·⁻¹) '' s = s⁻¹ := congr_fun (image_eq_preimage_of_inverse inv_involutive.leftInverse inv_involutive.rightInverse) _

