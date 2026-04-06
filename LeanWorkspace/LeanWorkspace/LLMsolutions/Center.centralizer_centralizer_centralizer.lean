import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem centralizer_centralizer_centralizer (S : Set M) :
    S.centralizer.centralizer.centralizer = S.centralizer := by
  ext x
  constructor
  · intro hx
    exact fun y hy => hx y <| Set.subset_centralizer_centralizer hy
  · intro hx
    exact fun y hy => (hy x hx).symm
