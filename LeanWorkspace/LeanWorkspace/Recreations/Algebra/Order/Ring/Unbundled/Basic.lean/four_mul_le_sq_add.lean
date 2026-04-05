import Mathlib

variable {R : Type u} {α : Type*}

variable [CommSemiring R] [LinearOrder R] {a d : R}

theorem four_mul_le_sq_add [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftReflectLE R] [AddLeftMono R]
    (a b : R) : 4 * a * b ≤ (a + b) ^ 2 := by
  calc 4 * a * b
    _ = 2 * a * b + 2 * a * b := by rw [mul_assoc, two_add_two_eq_four.symm, add_mul, mul_assoc]
    _ ≤ a ^ 2 + b ^ 2 + 2 * a * b := by gcongr; exact two_mul_le_add_sq _ _
    _ = a ^ 2 + 2 * a * b + b ^ 2 := by rw [add_right_comm]
    _ = (a + b) ^ 2 := (add_sq a b).symm

alias four_mul_le_pow_two_add := four_mul_le_sq_add

