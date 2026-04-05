import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [PartialOrder R] {a b c d : R}

variable [AddLeftReflectLT R]

theorem mul_add_mul_lt_mul_add_mul [ExistsAddOfLE R] [MulPosStrictMono R]
    [AddLeftStrictMono R]
    (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨d, hd, rfl⟩ := exists_pos_add_of_lt' hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  gcongr
  exact hd

