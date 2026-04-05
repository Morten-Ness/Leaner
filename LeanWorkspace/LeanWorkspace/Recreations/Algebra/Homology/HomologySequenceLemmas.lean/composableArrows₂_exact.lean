import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

theorem composableArrows₂_exact (hS₁ : S₁.ShortExact) (i : ι) :
    (HomologicalComplex.HomologySequence.composableArrows₂ S₁ i).Exact := (hS₁.homology_exact₂ i).exact_toComposableArrows

