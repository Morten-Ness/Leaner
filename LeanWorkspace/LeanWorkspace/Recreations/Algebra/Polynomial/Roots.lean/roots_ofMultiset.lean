import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_ofMultiset (s : Multiset R) : (ofMultiset s).roots = s := by
  simp

