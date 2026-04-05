import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem mul_eq_left (h : IsUnit a) : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := by rw [IsUnit.mul_right_inj h]

