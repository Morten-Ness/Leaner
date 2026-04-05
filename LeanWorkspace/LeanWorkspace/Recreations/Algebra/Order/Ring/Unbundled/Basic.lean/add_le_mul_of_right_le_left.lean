import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem add_le_mul_of_right_le_left [ZeroLEOneClass R] [NeZero (1 : R)]
    [AddLeftMono R] [PosMulStrictMono R]
    (b2 : 2 ≤ b) (ba : b ≤ a) : a + b ≤ a * b := have : 0 < a :=
    calc 0
      _ < 2 := zero_lt_two
      _ ≤ b := b2
      _ ≤ a := ba
  calc
    a + b ≤ a + a := by gcongr
    _ = a * 2 := (mul_two a).symm
    _ ≤ a * b := (mul_le_mul_iff_right₀ this).mpr b2

