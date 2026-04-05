import Mathlib

variable {α : Type*}

theorem unsym_comp_sym : (SymAlg.unsym : αˢʸᵐ → α) ∘ SymAlg.sym = id := rfl

