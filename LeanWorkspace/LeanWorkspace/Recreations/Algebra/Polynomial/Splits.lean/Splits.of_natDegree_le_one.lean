import Mathlib

variable {R : Type*}

variable [DivisionSemiring R]

theorem Splits.of_natDegree_le_one {f : R[X]} (hf : natDegree f ≤ 1) : Polynomial.Splits f := by
  obtain ⟨a, b, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hf
  by_cases ha : a = 0
  · simp_all
  · rw [← mul_inv_cancel_left₀ ha b, C_mul, ← mul_add]
    exact (X_add_C (a⁻¹ * b)).C_mul a

