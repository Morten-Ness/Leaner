import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_centralizer_centralizer (S : Set M) :
    S.centralizer.centralizer.centralizer = S.centralizer := by
  refine Set.Subset.antisymm ?_ Set.subset_centralizer_centralizer
  exact fun x hx y hy ↦ hx y <| Set.subset_centralizer_centralizer hy

