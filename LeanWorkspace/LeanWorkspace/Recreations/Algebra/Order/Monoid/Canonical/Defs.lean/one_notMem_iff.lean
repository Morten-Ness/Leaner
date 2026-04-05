import Mathlib

variable {α : Type u}

variable [MulOneClass α]

variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

theorem one_notMem_iff [OrderBot α] {s : Set α} : 1 ∉ s ↔ ∀ x ∈ s, 1 < x := bot_eq_one (α := α) ▸ bot_notMem_iff

alias Ne.pos := pos_of_ne_zero

