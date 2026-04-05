import Mathlib

variable {α : Type*}

theorem sym_surjective : Function.Surjective (SymAlg.sym : α → αˢʸᵐ) := SymAlg.sym.surjective

