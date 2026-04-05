import Mathlib

variable {α : Type*}

theorem unsym_surjective : Function.Surjective (SymAlg.unsym : αˢʸᵐ → α) := SymAlg.unsym.surjective

