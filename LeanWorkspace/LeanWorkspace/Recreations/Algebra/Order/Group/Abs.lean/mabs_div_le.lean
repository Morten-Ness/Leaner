import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_le (a b c : G) : |a / c|ₘ ≤ |a / b|ₘ * |b / c|ₘ := calc
    |a / c|ₘ = |a / b * (b / c)|ₘ := by rw [div_mul_div_cancel]
    _ ≤ |a / b|ₘ * |b / c|ₘ := mabs_mul_le _ _

