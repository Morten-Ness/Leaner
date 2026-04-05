import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_insert_intCast (n : ℤ) (s : Set A) : Algebra.adjoin R (insert (n : A) s) = Algebra.adjoin R s := by
  simpa using Algebra.adjoin_insert_algebraMap (n : R) s

