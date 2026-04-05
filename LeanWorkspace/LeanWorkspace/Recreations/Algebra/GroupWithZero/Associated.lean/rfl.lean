import Mathlib

variable {M : Type*}

theorem rfl [Monoid M] {x : M} : x ~ᵤ x := .refl x

