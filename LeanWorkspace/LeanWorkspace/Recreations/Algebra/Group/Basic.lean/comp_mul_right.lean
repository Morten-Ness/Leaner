import Mathlib

variable {α β G M : Type*}

variable [Semigroup α]

theorem comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) := by
  ext z
  simp [mul_assoc]

