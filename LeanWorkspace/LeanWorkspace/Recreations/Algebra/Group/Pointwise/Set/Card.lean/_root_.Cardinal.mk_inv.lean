import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [InvolutiveInv G]

theorem _root_.Cardinal.mk_inv (s : Set G) : #↥(s⁻¹) = #s := by
  rw [← image_inv_eq_inv, Cardinal.mk_image_eq_of_injOn _ _ inv_injective.injOn]

