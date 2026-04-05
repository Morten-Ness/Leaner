import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_le_one : |a / b|ₘ ≤ 1 ↔ a = b := ⟨eq_of_mabs_div_le_one, by rintro rfl; rw [div_self', mabs_one]⟩

