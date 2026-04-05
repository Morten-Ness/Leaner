import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem div_lt_of_mabs_div_lt_right (h : |a / b|ₘ < c) : a / c < b := div_lt_of_mabs_div_lt_left (mabs_div_comm a b ▸ h)

