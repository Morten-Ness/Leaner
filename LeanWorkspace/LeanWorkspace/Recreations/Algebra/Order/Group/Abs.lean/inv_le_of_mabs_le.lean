import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem inv_le_of_mabs_le (h : |a|ₘ ≤ b) : b⁻¹ ≤ a := (mabs_le.mp h).1

