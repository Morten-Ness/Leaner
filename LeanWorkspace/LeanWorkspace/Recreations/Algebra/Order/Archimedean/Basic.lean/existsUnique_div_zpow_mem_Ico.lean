import Mathlib

variable {G M R K : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

theorem existsUnique_div_zpow_mem_Ico {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b / a ^ m ∈ Set.Ico c (c * a) := by
  simpa only [mem_Ico, le_div_iff_mul_le, one_mul, mul_comm c, div_lt_iff_lt_mul, mul_assoc] using
    existsUnique_zpow_near_of_one_lt' ha (b / c)

