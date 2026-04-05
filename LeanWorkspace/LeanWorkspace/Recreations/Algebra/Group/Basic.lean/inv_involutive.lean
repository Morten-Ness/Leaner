import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem inv_involutive : Function.Involutive (Inv.inv : G → G) := inv_inv

