import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem nthRootsFinset_toSet {n : ℕ} (h : 0 < n) (a : R) :
    Polynomial.nthRootsFinset n a = {r | r ^ n = a} := by
  ext x
  simp_all

