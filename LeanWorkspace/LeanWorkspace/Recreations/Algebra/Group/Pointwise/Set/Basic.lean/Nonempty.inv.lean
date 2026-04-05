import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem Nonempty.inv (h : s.Nonempty) : s⁻¹.Nonempty := Set.nonempty_inv.2 h

