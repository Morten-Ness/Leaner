import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

variable {n : ℕ} (S : ComposableArrows C n)

theorem exact_of_iso {S₁ S₂ : CategoryTheory.ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) :
    S₂.Exact where
  toIsComplex := CategoryTheory.ComposableArrows.isComplex_of_iso e h₁.toIsComplex
  exact i hi := ShortComplex.exact_of_iso (CategoryTheory.ComposableArrows.scMapIso e h₁.toIsComplex
    (CategoryTheory.ComposableArrows.isComplex_of_iso e h₁.toIsComplex) i) (h₁.exact i hi)

