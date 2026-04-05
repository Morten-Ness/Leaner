import Mathlib

variable {α : Type*}

theorem sym_injective : Function.Injective (SymAlg.sym : α → αˢʸᵐ) := SymAlg.sym.injective

