import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem nthRootsFinset_def (n : ℕ) {R : Type*} (a : R) [CommRing R] [IsDomain R] [DecidableEq R] :
    Polynomial.nthRootsFinset n a = Multiset.toFinset (Polynomial.nthRoots n a) := by
  unfold Polynomial.nthRootsFinset
  convert rfl

