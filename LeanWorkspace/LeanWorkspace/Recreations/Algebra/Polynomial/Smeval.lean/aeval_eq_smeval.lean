import Mathlib

theorem aeval_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) (p : R[X]) : aeval x p = p.smeval x := by
  rw [aeval_def, eval₂_def, Algebra.algebraMap_eq_smul_one', smeval_def]
  simp only [Algebra.smul_mul_assoc, one_mul]
  exact rfl

