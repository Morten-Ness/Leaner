import Mathlib

variable {R M M' N N' P P' : Type*}

variable (f : M → N) (g : N → P) (g' : P → P')

theorem iff_rangeFactorization [One P] (hg : 1 ∈ Set.range g) :
    letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
    Function.MulExact f g ↔ Function.MulExact ((↑) : Set.range f → N) (Set.rangeFactorization g) := by
  letI : One (Set.range g) := ⟨⟨1, hg⟩⟩
  have : ((1 : Set.range g) : P) = 1 := rfl
  simp [Function.MulExact, Set.rangeFactorization, Subtype.ext_iff, this]

