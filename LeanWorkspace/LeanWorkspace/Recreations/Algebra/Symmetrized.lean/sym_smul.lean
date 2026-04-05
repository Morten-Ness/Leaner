import Mathlib

variable {α : Type*}

theorem sym_smul {R : Type*} [SMul R α] (c : R) (a : α) : SymAlg.sym (c • a) = c • SymAlg.sym a := rfl

