import Mathlib

variable {α : Type*}

theorem unsym_symm : (@SymAlg.unsym α).symm = SymAlg.sym := rfl

