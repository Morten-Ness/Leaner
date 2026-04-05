import Mathlib

variable {α : Type*}

theorem sym_symm : (@SymAlg.sym α).symm = SymAlg.unsym := rfl

