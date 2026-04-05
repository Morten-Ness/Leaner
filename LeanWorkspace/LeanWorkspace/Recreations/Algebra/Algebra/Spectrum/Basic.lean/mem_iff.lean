import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem mem_iff {r : R} {a : A} : r ∈ σ a ↔ ¬IsUnit (↑ₐ r - a) := Iff.rfl

