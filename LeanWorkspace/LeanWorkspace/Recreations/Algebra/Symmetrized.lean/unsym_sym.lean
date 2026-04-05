import Mathlib

variable {α : Type*}

theorem unsym_sym (a : α) : SymAlg.unsym (SymAlg.sym a) = a := rfl

