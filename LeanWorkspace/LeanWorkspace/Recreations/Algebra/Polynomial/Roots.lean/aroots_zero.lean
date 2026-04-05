import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).aroots S = 0 := by
  rw [← C_0, Polynomial.aroots_C]

