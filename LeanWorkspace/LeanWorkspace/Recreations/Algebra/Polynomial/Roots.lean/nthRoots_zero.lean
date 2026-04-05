import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem nthRoots_zero (r : R) : Polynomial.nthRoots 0 r = 0 := by
  simp only [pow_zero, Polynomial.nthRoots, ← C_1, ← C_sub, Polynomial.roots_C]

