import Mathlib

variable {M : Type*}

theorem refl [Monoid M] (x : M) : x ~ᵤ x := ⟨1, by simp⟩

