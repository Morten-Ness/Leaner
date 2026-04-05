import Mathlib

variable {α : Type*}

theorem unsym_neg [Neg α] (a : αˢʸᵐ) : SymAlg.unsym (-a) = -SymAlg.unsym a := rfl

