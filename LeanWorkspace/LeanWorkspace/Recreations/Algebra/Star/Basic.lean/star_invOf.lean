import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Invertible r]
    [Invertible (star r)] : star (⅟r) = ⅟(star r) := by
  have : star (⅟r) = star (⅟r) * ((star r) * ⅟(star r)) := by
    simp only [mul_invOf_self, mul_one]
  rw [this, ← mul_assoc]
  have : (star (⅟r)) * (star r) = star 1 := by rw [← star_mul, mul_invOf_self]
  rw [this, star_one, one_mul]

