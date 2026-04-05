import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.degree_eq_card_roots (hf : Polynomial.Splits f) (hf0 : f ≠ 0) :
    f.degree = f.roots.card := (degree_eq_iff_natDegree_eq hf0).mpr hf.natDegree_eq_card_roots

