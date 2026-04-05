import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem one_mem_nthRootsFinset (hn : 0 < n) : 1 ∈ Polynomial.nthRootsFinset n (1 : R) := by
  rw [Polynomial.mem_nthRootsFinset hn, one_pow]

