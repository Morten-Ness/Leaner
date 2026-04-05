import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty := inv_involutive.surjective.nonempty_preimage

