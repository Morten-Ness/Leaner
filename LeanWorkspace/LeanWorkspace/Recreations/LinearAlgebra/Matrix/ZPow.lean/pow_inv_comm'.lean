import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem pow_inv_comm' (A : M) (m n : ℕ) : A⁻¹ ^ m * A ^ n = A ^ n * A⁻¹ ^ m := by
  induction n generalizing m with
  | zero => simp
  | succ n IH =>
    rcases m with m | m
    · simp
    rcases nonsing_inv_cancel_or_zero A with ⟨h, h'⟩ | h
    · calc
        A⁻¹ ^ (m + 1) * A ^ (n + 1) = A⁻¹ ^ m * (A⁻¹ * A) * A ^ n := by
          simp only [pow_succ A⁻¹, pow_succ' A, Matrix.mul_assoc]
        _ = A ^ n * A⁻¹ ^ m := by simp only [h, Matrix.mul_one, IH m]
        _ = A ^ n * (A * A⁻¹) * A⁻¹ ^ m := by simp only [h', Matrix.mul_one]
        _ = A ^ (n + 1) * A⁻¹ ^ (m + 1) := by
          simp only [pow_succ A, pow_succ' A⁻¹, Matrix.mul_assoc]
    · simp [h]

