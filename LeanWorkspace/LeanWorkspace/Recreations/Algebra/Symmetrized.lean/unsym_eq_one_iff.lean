import Mathlib

variable {α : Type*}

theorem unsym_eq_one_iff [One α] (a : αˢʸᵐ) : SymAlg.unsym a = 1 ↔ a = 1 := SymAlg.unsym_injective.eq_iff' rfl

