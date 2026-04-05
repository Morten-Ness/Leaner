import Mathlib

variable {α : Type*}

theorem sym_eq_one_iff [One α] (a : α) : SymAlg.sym a = 1 ↔ a = 1 := SymAlg.sym_injective.eq_iff' rfl

