import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem splits_of_natDegree_le_one_of_invertible {f : R[X]}
    (hf : f.natDegree ≤ 1) (h : Invertible f.leadingCoeff) : f.Splits := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · replace h : Invertible a := by simpa [leadingCoeff, ha] using h
    rw [← mul_invOf_cancel_left a b, C_mul, ← mul_add]
    exact (Polynomial.Splits.C a).mul (Polynomial.Splits.X_add_C _)

