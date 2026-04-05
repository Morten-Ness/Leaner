import Mathlib

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

variable (G) [Nontrivial G] [IsCyclic G]

theorem genLTOne_unique {g : G} (hg : g < 1) (htop : Subgroup.zpowers g = ⊤) : g = LinearOrderedCommGroup.genLTOne G := LinearOrderedCommGroup.Subgroup.genLTOne_unique (⊤ : Subgroup G) hg htop

