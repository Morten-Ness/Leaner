import Mathlib

variable {α : Type*}

theorem sym_comp_unsym : (SymAlg.sym : α → αˢʸᵐ) ∘ SymAlg.unsym = id := rfl

