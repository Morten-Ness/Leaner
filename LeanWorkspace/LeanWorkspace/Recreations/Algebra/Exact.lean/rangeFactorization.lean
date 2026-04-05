import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem rangeFactorization [One P] (h : Function.MulExact f g) (hg : 1 ∈ Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    Function.MulExact ((↑) : Set.range f → N) (Set.rangeFactorization g) :=
  (Function.MulExact.iff_rangeFactorization hg).1 h

