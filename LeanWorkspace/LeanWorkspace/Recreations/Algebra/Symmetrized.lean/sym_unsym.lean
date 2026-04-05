import Mathlib

variable {α : Type*}

theorem sym_unsym (a : α) : SymAlg.sym (SymAlg.unsym a) = a := rfl

