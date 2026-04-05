import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [Group α] {a b : α}

variable [MulLeftMono α]

theorem oneLePart_leOnePart_inj : a⁺ᵐ = b⁺ᵐ ∧ a⁻ᵐ = b⁻ᵐ ↔ a = b := Prod.mk_inj.symm.trans oneLePart_leOnePart_injective.eq_iff

