import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.roots_ne_zero (hf : Polynomial.Splits f) (hf0 : natDegree f ≠ 0) :
    f.roots ≠ 0 := by
  simpa [hf.natDegree_eq_card_roots] using hf0

