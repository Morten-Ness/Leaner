import Mathlib

variable {α : Type*}

theorem unsym_ne_one_iff [One α] (a : αˢʸᵐ) : SymAlg.unsym a ≠ (1 : α) ↔ a ≠ (1 : αˢʸᵐ) := not_congr <| SymAlg.unsym_eq_one_iff a

