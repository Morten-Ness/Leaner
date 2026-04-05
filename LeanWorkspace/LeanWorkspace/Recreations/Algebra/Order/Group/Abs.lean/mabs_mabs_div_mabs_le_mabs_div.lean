import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_mabs_div_mabs_le_mabs_div (a b : G) : |(|a|ₘ / |b|ₘ)|ₘ ≤ |a / b|ₘ := mabs_div_le_iff.2
    ⟨mabs_div_mabs_le_mabs_div _ _, by rw [mabs_div_comm]; apply mabs_div_mabs_le_mabs_div⟩

