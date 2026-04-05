import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem eq_of_mabs_div_le_one (h : |a / b|ₘ ≤ 1) : a = b := eq_of_mabs_div_eq_one (le_antisymm h (one_le_mabs (a / b)))

