import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_div_pos : 1 < |a / b|ₘ ↔ a ≠ b := not_le.symm.trans mabs_div_le_one.not

