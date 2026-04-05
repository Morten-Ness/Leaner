import Mathlib

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

variable (G) [Nontrivial G] [IsCyclic G]

theorem genLTOne_eq_of_top : LinearOrderedCommGroup.genLTOne G = (⊤ : Subgroup G).genLTOne := rfl

