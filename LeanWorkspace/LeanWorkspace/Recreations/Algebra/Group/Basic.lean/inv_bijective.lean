import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem inv_bijective : Function.Bijective (Inv.inv : G → G) := inv_involutive.bijective

