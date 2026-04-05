import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem rootSet_one (S) [CommRing S] [IsDomain S] [Algebra T S] : (1 : T[X]).rootSet S = ∅ := by
  rw [← C_1, Polynomial.rootSet_C]

