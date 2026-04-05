import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem aroots_X_sub_C [CommRing S] [IsDomain S] [Algebra T S]
    (r : T) : aroots (X - C r) S = {algebraMap T S r} := by
  rw [Polynomial.aroots_def, Polynomial.map_sub, map_X, map_C, Polynomial.roots_X_sub_C]

