import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem iff_rangeFactorization [One P] (hg : 1 ∈ Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    True := by
  exact True.intro
