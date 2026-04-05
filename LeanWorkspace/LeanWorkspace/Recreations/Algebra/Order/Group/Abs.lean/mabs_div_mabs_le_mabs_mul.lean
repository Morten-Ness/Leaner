import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_mabs_le_mabs_mul (a b : G) : |a|ₘ / |b|ₘ ≤ |a * b|ₘ := mabs_inv b ▸ div_inv_eq_mul a b ▸ mabs_div_mabs_le_mabs_div a b⁻¹

