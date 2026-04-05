import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem ofMultiset_injective : Function.Injective (ofMultiset (R := R)) :=
  Polynomial.rightInverse_ofMultiset_roots R |>.injective

