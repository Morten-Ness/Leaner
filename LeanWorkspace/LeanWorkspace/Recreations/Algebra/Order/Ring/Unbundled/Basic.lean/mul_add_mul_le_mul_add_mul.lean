import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

theorem mul_add_mul_le_mul_add_mul [ExistsAddOfLE R] [MulPosMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_nonneg_add_of_le hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  gcongr
  assumption

