import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem count_roots [DecidableEq R] (p : R[X]) : p.roots.count a = rootMultiplicity a p := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  rw [Polynomial.roots_def, dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a

