import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

theorem mono_homologyMap_τ₃ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Mono (homologyMap φ.τ₂ i))
    (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Mono (homologyMap φ.τ₃ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply mono_of_epi_of_mono_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ i j hij).δlast.δlast
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ i j hij).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ _ hij
  · refine mono_of_epi_of_epi_of_mono (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ i)
      (HomologicalComplex.HomologySequence.composableArrows₂_exact hS₁ i) (HomologicalComplex.HomologySequence.composableArrows₂_exact hS₂ i) ?_ h₁ h₂
    have := hS₁.epi_g
    apply epi_homologyMap_of_epi_of_not_rel
    simpa using hi

