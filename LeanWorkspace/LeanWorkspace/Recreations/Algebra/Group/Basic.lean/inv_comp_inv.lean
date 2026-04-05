import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G := inv_involutive.comp_self

