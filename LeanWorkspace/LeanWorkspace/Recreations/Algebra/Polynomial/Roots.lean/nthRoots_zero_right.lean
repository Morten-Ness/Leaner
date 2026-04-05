import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem nthRoots_zero_right {R} [CommRing R] [IsDomain R] (n : ℕ) :
    Polynomial.nthRoots n (0 : R) = Multiset.replicate n 0 := by
  rw [Polynomial.nthRoots, C.map_zero, sub_zero, Polynomial.roots_pow, Polynomial.roots_X, Multiset.nsmul_singleton]

