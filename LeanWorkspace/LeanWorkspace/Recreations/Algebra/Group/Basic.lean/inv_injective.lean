import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem inv_injective : Function.Injective (Inv.inv : G → G) := inv_involutive.injective

