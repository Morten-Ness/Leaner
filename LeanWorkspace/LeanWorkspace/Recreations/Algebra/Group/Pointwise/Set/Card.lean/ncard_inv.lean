import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [InvolutiveInv G]

theorem ncard_inv (s : Set G) : s⁻¹.ncard = s.ncard := by simp [ncard]

