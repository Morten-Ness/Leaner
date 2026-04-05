import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ := inv_involutive.eq_iff

