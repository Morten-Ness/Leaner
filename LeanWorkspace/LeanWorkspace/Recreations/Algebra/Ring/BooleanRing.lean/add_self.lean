import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] (a b : α)

theorem add_self : a + a = 0 := by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by rw [BooleanRing.mul_self]
      _ = a * a + a * a + (a * a + a * a) := by rw [add_mul, mul_add]
      _ = a + a + (a + a) := by rw [BooleanRing.mul_self]
  rwa [right_eq_add] at this

