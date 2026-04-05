import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem mul_add_mul_le_mul_add_mul' [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hba : b ≤ a) (hdc : d ≤ c) : a * d + b * c ≤ a * c + b * d := by
  rw [add_comm (a * d), add_comm (a * c)]; exact mul_add_mul_le_mul_add_mul hba hdc

