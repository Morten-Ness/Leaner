import Mathlib

variable {α : Type u}

theorem mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible a} : a * ⅟a = 1 := Invertible.mul_invOf_self

