import Mathlib

variable {α : Type*}

theorem unsym_smul {R : Type*} [SMul R α] (c : R) (a : αˢʸᵐ) : SymAlg.unsym (c • a) = c • SymAlg.unsym a := rfl

