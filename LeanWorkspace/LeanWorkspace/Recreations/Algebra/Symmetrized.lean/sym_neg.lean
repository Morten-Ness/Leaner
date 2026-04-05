import Mathlib

variable {α : Type*}

theorem sym_neg [Neg α] (a : α) : SymAlg.sym (-a) = -SymAlg.sym a := rfl

