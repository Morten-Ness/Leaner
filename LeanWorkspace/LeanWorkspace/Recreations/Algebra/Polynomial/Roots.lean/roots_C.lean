import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_C (x : R) : (C x).roots = 0 := by
  classical exact
  if H : x = 0 then by rw [H, C_0, Polynomial.roots_zero]
  else
    Multiset.ext.mpr fun r => (by
      rw [Polynomial.count_roots, count_zero, rootMultiplicity_eq_zero (not_isRoot_C _ _ H)])

