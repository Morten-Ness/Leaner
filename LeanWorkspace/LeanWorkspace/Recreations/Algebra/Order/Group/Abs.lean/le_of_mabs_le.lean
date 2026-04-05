import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem le_of_mabs_le (h : |a|ₘ ≤ b) : a ≤ b := (mabs_le.mp h).2

