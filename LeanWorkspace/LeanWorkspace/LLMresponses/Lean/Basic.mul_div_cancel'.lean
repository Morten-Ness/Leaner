FAIL
import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mul_div_cancel' {a b : R} (hb : b ≠ 0) (hab : b ∣ a) : b * (a / b) = a := by
  obtain ⟨c, rfl⟩ := hab
  rw [mul_assoc, EuclideanDomain.mul_div_right _ hb]
