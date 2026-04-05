import Mathlib

variable {α β G M : Type*}

variable [Semigroup α]

theorem comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·) := by
  ext z
  simp [mul_assoc]

