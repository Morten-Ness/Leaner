import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

theorem epi_homologyMap_τ₃ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₂ i))
    (h₂ : ∀ j, c.Rel i j → Epi (homologyMap φ.τ₁ j))
    (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₂ j)) :
    Epi (homologyMap φ.τ₃ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply epi_of_epi_of_epi_of_mono
      ((δ₀Functor ⋙ δlastFunctor).map (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ i j hij).δ₀.δlast
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ i j hij).δ₀.δlast
    · exact h₁
    · exact h₂ j hij
    · exact h₃ j hij
  · have := hS₂.epi_g
    have eq := (homologyFunctor C _ i).congr_map φ.comm₂₃
    dsimp at eq
    simp only [homologyMap_comp] at eq
    have := epi_homologyMap_of_epi_of_not_rel S₂.g i (by simpa using hi)
    exact epi_of_epi_fac eq.symm

