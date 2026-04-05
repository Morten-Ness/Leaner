import Mathlib

variable {α : Type*}

theorem unsym_injective : Function.Injective (SymAlg.unsym : αˢʸᵐ → α) := SymAlg.unsym.injective

