import Mathlib

variable {M M₂ : Type*}

theorem NNRat.cast_smul_eq_nnqsmul (R : Type*) [DivisionSemiring R]
    [MulAction R M] [MulAction ℚ≥0 M] [IsScalarTower ℚ≥0 R M]
    (q : ℚ≥0) (x : M) : (q : R) • x = q • x := by
  rw [← one_smul R x, ← smul_assoc, ← smul_assoc]; simp

