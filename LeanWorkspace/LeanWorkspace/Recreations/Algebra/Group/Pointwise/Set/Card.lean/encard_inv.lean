import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [InvolutiveInv G]

theorem encard_inv (s : Set G) : s⁻¹.encard = s.encard := by
  simp [← toENat_cardinalMk]

