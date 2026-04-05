import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (C a).aroots S = 0 := by
  rw [Polynomial.aroots_def, map_C, Polynomial.roots_C]

