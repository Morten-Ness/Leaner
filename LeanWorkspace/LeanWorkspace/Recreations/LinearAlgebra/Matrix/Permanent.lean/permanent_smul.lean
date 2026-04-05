import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_smul (M : Matrix n n R) (c : R) :
    Matrix.permanent (c • M) = c ^ Fintype.card n * Matrix.permanent M := by
  simp only [Matrix.permanent, smul_apply, smul_eq_mul, Finset.mul_sum]
  congr
  ext
  rw [mul_comm]
  conv in ∏ _, c * _ => simp [mul_comm c];
  exact prod_mul_pow_card.symm

