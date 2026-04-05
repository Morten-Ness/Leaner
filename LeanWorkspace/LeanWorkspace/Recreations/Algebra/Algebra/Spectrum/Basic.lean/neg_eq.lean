import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem neg_eq (a : A) : -σ a = σ (-a) := by
  rw [spectrum, Set.compl_neg, spectrum, resolventSet_neg]

