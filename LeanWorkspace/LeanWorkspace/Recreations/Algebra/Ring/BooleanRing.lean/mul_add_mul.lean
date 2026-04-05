import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] (a b : α)

theorem mul_add_mul : a * b + b * a = 0 := by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by rw [BooleanRing.mul_self]
      _ = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
      _ = a + a * b + (b * a + b) := by simp only [BooleanRing.mul_self]
      _ = a + b + (a * b + b * a) := by abel
  rwa [left_eq_add] at this

