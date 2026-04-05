import Mathlib

variable {G M R K : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

theorem existsUnique_add_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b * a ^ m ∈ Set.Ioc c (c * a) := (Equiv.addRight (1 : ℤ)).bijective.existsUnique_iff.2 <| by
    simpa only [zpow_add_one, div_lt_iff_lt_mul', le_div_iff_mul_le', ← mul_assoc, and_comm,
      mem_Ioc, Equiv.coe_addRight, mul_le_mul_iff_right] using
      existsUnique_zpow_near_of_one_lt ha (c / b)

