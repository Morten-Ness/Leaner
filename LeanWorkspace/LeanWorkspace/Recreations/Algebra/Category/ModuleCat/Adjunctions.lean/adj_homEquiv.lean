import Mathlib

variable (R : Type u)

variable [Ring R]

theorem adj_homEquiv (X : Type u) (M : ModuleCat.{u} R) :
    (ModuleCat.adj R).homEquiv X M = ModuleCat.freeHomEquiv := by
  simp only [ModuleCat.adj, Adjunction.mkOfHomEquiv_homEquiv]

