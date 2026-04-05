import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [InvolutiveInv G]

theorem natCard_inv (s : Set G) : Nat.card ↥(s⁻¹) = Nat.card s := by simp

