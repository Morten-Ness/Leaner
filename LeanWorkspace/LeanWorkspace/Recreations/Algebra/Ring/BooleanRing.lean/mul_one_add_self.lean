import Mathlib

open scoped symmDiff

variable {α β γ : Type*}

variable [BooleanRing α] (a b : α)

theorem mul_one_add_self : a * (1 + a) = 0 := by rw [mul_add, mul_one, BooleanRing.mul_self, BooleanRing.add_self]

-- Note [lower instance priority]

