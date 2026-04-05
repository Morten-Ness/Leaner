import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem rightInverse_ofMultiset_roots : Function.RightInverse (α := R[X]) ofMultiset Polynomial.roots :=
  Polynomial.roots_ofMultiset

