import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem nthRootsFinset_zero (a : R) : Polynomial.nthRootsFinset 0 a = ∅ := by
  classical simp [Polynomial.nthRootsFinset_def]

