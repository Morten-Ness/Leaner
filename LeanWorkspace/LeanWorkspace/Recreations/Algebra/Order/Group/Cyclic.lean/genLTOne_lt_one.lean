import Mathlib

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

theorem genLTOne_lt_one : H.genLTOne < 1 := H.exists_generator_lt_one.choose_spec.1

