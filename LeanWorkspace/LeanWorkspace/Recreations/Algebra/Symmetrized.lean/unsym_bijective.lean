import Mathlib

variable {α : Type*}

theorem unsym_bijective : Function.Bijective (SymAlg.unsym : αˢʸᵐ → α) := SymAlg.unsym.symm.bijective

