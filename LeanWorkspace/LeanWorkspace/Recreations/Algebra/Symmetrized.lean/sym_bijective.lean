import Mathlib

variable {α : Type*}

theorem sym_bijective : Function.Bijective (SymAlg.sym : α → αˢʸᵐ) := SymAlg.sym.bijective

