import Mathlib

variable {α : Type*}

theorem sym_ne_one_iff [One α] (a : α) : SymAlg.sym a ≠ (1 : αˢʸᵐ) ↔ a ≠ (1 : α) := not_congr <| SymAlg.sym_eq_one_iff a

