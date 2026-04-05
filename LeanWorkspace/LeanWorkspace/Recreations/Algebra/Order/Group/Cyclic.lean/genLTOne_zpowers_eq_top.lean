import Mathlib

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

theorem genLTOne_zpowers_eq_top : LinearOrderedCommGroup.Subgroup.zpowers H.genLTOne = H := H.exists_generator_lt_one.choose_spec.2

