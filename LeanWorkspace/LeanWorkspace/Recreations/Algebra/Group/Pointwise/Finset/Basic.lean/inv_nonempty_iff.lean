import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

theorem inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty := image_nonempty

alias ⟨Nonempty.of_inv, Nonempty.inv⟩ := inv_nonempty_iff

attribute [to_additive] Nonempty.inv Nonempty.of_inv
attribute [aesop safe apply (rule_sets := [finsetNonempty])] Nonempty.inv Nonempty.neg

