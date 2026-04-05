import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_mabs_le_mabs_div (a b : G) : |a|ₘ / |b|ₘ ≤ |a / b|ₘ := div_le_iff_le_mul.2 <|
    calc
      |a|ₘ = |a / b * b|ₘ := by rw [div_mul_cancel]
      _ ≤ |a / b|ₘ * |b|ₘ := mabs_mul_le _ _

