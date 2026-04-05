import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mem_nthRootsFinset {n : ℕ} (h : 0 < n) (a : R) {x : R} :
    x ∈ Polynomial.nthRootsFinset n a ↔ x ^ (n : ℕ) = a := by
  classical
  rw [Polynomial.nthRootsFinset_def, mem_toFinset, Polynomial.mem_nthRoots h]

