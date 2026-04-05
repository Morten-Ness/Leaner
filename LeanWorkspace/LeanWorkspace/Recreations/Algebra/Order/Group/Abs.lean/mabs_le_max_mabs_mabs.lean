import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_le_max_mabs_mabs (hab : a ≤ b) (hbc : b ≤ c) : |b|ₘ ≤ max |a|ₘ |c|ₘ := mabs_le'.2
    ⟨by simp [hbc.trans (le_mabs_self c)], by
      simp [(inv_le_inv_iff.mpr hab).trans (inv_le_mabs a)]⟩

