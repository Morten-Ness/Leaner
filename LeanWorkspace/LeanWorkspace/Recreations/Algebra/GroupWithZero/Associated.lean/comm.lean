import Mathlib

variable {M : Type*}

theorem comm [Monoid M] {x y : M} : x ~ᵤ y ↔ y ~ᵤ x := ⟨Associated.symm, Associated.symm⟩

