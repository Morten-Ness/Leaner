import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_singleton_intCast (n : ℤ) : R[n : A] = ⊥ := by
  simpa using Algebra.adjoin_singleton_algebraMap A (n : R)

