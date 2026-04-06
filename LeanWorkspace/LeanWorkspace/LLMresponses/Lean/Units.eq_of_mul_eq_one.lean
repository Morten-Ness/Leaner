FAIL
import Mathlib

variable {u v : ℤ}

theorem eq_of_mul_eq_one (h : u * v = 1) : u = v := by
  have hu : u = 1 ∨ u = -1 := by
    nlinarith [sq_nonneg (u - 1), sq_nonneg (u + 1), h]
  rcases hu with rfl | rfl
  · have hv : v = 1 := by linarith
    simp [hv]
  · have hv : v = -1 := by linarith
    simp [hv]
