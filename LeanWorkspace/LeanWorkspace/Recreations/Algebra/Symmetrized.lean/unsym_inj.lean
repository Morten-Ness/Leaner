import Mathlib

variable {α : Type*}

theorem unsym_inj {a b : αˢʸᵐ} : SymAlg.unsym a = SymAlg.unsym b ↔ a = b := SymAlg.unsym_injective.eq_iff

