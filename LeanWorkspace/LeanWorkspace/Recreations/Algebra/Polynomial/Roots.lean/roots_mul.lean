import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add, Polynomial.count_roots, Polynomial.count_roots, Polynomial.count_roots, rootMultiplicity_mul hpq]

