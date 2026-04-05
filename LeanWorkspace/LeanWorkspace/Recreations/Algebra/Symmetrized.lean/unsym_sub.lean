import Mathlib

variable {α : Type*}

theorem unsym_sub [Sub α] (a b : αˢʸᵐ) : SymAlg.unsym (a - b) = SymAlg.unsym a - SymAlg.unsym b := rfl

