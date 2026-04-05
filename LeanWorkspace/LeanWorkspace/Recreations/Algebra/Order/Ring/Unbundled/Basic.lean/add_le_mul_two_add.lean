import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [Preorder R] {a b c d : R}

theorem add_le_mul_two_add [ZeroLEOneClass R] [MulPosMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) := calc
    a + (2 + b) ≤ a + (a + a * b) := by
      gcongr; exact le_mul_of_one_le_left b0 <| one_le_two.trans a2
    _ ≤ a * (2 + b) := by rw [mul_add, mul_two, add_assoc]

