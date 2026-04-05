import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mul_div_cancel' {a b : R} (hb : b ≠ 0) (hab : b ∣ a) : b * (a / b) = a := by
  rw [← EuclideanDomain.mul_div_assoc _ hab, mul_div_cancel_left₀ _ hb]

-- This generalizes `Int.div_one`, see note [simp-normal form]

