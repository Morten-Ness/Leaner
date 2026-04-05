import Mathlib

variable {M M₂ : Type*}

theorem Rat.cast_smul_eq_qsmul (R : Type*) [DivisionRing R]
    [MulAction R M] [MulAction ℚ M] [IsScalarTower ℚ R M]
    (q : ℚ) (x : M) : (q : R) • x = q • x := by
  rw [← one_smul R x, ← smul_assoc, ← smul_assoc]; simp

