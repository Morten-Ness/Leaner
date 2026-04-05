import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_mul' (a b : G) : |a|ₘ ≤ |b|ₘ * |b * a|ₘ := by simpa using mabs_mul_le b⁻¹ (b * a)

