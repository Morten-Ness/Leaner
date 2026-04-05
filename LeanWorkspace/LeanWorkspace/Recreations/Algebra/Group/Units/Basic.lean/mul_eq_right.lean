import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem mul_eq_right (h : IsUnit b) : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := by rw [IsUnit.mul_left_inj h]

