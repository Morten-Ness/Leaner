import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_nonneg_of_three [ExistsAddOfLE R] [MulPosStrictMono R] [PosMulStrictMono R]
    [AddLeftMono R] [AddLeftReflectLE R]
    (a b c : R) : 0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a := by
  iterate 3 rw [mul_nonneg_iff]
  have or_a := le_total 0 a
  have or_b := le_total 0 b
  have or_c := le_total 0 c
  aesop

