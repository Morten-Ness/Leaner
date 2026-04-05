import Mathlib

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

theorem genLTOne_mem : H.genLTOne ∈ H := by
  nth_rewrite 1 [← H.genLTOne_zpowers_eq_top]
  exact LinearOrderedCommGroup.Subgroup.mem_zpowers (LinearOrderedCommGroup.Subgroup.genLTOne H)

