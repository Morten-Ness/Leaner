import Mathlib

variable {α : Type*}

theorem sym_add [Add α] (a b : α) : SymAlg.sym (a + b) = SymAlg.sym a + SymAlg.sym b := rfl

