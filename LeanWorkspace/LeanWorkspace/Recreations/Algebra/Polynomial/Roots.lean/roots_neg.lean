import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_neg (p : R[X]) : (-p).roots = p.roots := by
  rw [← neg_one_smul R p, Polynomial.roots_smul_nonzero p (neg_ne_zero.mpr one_ne_zero)]

