import Mathlib

variable {α : Type*}

theorem sym_inj {a b : α} : SymAlg.sym a = SymAlg.sym b ↔ a = b := SymAlg.sym_injective.eq_iff

