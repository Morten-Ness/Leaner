import Mathlib

variable {G M R K : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

theorem existsUnique_sub_zpow_mem_Ioc {a : G} (ha : 1 < a) (b c : G) :
    ∃! m : ℤ, b / a ^ m ∈ Set.Ioc c (c * a) := (Equiv.neg ℤ).bijective.existsUnique_iff.2 <| by
    simpa only [Equiv.neg_apply, zpow_neg, div_inv_eq_mul] using
      existsUnique_add_zpow_mem_Ioc ha b c

