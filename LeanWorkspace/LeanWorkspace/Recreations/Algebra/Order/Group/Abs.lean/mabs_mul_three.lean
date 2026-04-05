import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_mul_three (a b c : G) : |a * b * c|ₘ ≤ |a|ₘ * |b|ₘ * |c|ₘ := by
  grw [mabs_mul_le, mabs_mul_le]

