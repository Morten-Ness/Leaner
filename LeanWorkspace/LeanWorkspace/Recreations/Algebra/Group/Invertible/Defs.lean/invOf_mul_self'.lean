import Mathlib

variable {α : Type u}

theorem invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible a} : ⅟a * a = 1 := Invertible.invOf_mul_self

