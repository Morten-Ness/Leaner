import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b := inv_injective.eq_iff

