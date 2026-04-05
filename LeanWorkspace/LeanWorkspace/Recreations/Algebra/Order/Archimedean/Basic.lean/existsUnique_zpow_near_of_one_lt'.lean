import Mathlib

variable {G M R K : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

theorem existsUnique_zpow_near_of_one_lt' {a : G} (ha : 1 < a) (g : G) :
    ∃! k : ℤ, 1 ≤ g / a ^ k ∧ g / a ^ k < a := by
  simpa only [one_le_div', zpow_add_one, div_lt_iff_lt_mul'] using
    existsUnique_zpow_near_of_one_lt ha g

