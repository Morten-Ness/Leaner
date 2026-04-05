import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem inv_surjective : Function.Surjective (Inv.inv : G → G) := inv_involutive.surjective

