import Mathlib

variable {G M S : Type*}

variable [Mul S]

theorem symm_iff {a b : S} : Commute a b ↔ Commute b a := ⟨Commute.symm, Commute.symm⟩

