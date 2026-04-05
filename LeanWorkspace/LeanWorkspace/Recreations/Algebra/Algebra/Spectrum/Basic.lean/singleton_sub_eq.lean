import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem singleton_sub_eq (a : A) (r : R) : {r} - σ a = σ (↑ₐ r - a) := by
  rw [sub_eq_add_neg, spectrum.neg_eq, spectrum.singleton_add_eq, sub_eq_add_neg]

