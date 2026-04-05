import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem add_le_mul_of_left_le_right [ZeroLEOneClass R] [NeZero (1 : R)]
    [MulPosStrictMono R] [AddLeftMono R]
    (a2 : 2 ≤ a) (ab : a ≤ b) : a + b ≤ a * b := have : 0 < b :=
    calc
      0 < 2 := zero_lt_two
      _ ≤ a := a2
      _ ≤ b := ab
  calc
    a + b ≤ b + b := by gcongr
    _ = 2 * b := (two_mul b).symm
    _ ≤ a * b := (mul_le_mul_iff_left₀ this).mpr a2

