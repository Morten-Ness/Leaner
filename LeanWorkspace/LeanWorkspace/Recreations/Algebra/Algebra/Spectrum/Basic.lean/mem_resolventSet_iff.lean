import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem mem_resolventSet_iff {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (↑ₐ r - a) := Iff.rfl

