import Mathlib

variable {u v : ℤ}

theorem isUnit_mul_self (hu : IsUnit u) : u * u = 1 := by
  rcases hu with ⟨a, rfl⟩
  fin_cases a <;> decide
