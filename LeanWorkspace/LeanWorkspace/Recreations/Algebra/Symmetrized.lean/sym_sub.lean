import Mathlib

variable {α : Type*}

theorem sym_sub [Sub α] (a b : α) : SymAlg.sym (a - b) = SymAlg.sym a - SymAlg.sym b := rfl

