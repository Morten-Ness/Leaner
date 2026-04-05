import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z) := by
  by_cases hz : z = 0
  · subst hz
    rw [div_zero, div_zero, mul_zero]
  rcases h with ⟨p, rfl⟩
  rw [mul_div_cancel_left₀ _ hz, mul_left_comm, mul_div_cancel_left₀ _ hz]

