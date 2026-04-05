import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {C} {A : C}

theorem isIso_homologyMap_of_isIso_cyclesMap_of_epi {φ : S₁ ⟶ S₂}
    [S₁.HasHomology] [S₂.HasHomology] (h₁ : IsIso (cyclesMap φ)) (h₂ : Epi φ.τ₁) :
    IsIso (CategoryTheory.ShortComplex.homologyMap φ) := by
  have h : S₂.toCycles ≫ inv (cyclesMap φ) ≫ S₁.homologyπ = 0 := by
    simp only [← cancel_epi φ.τ₁, ← toCycles_naturality_assoc,
      IsIso.hom_inv_id_assoc, CategoryTheory.ShortComplex.toCycles_comp_homologyπ, comp_zero]
  have ⟨z, hz⟩ := CokernelCofork.IsColimit.desc' S₂.homologyIsCokernel _ h
  dsimp at hz
  refine ⟨⟨z, ?_, ?_⟩⟩
  · rw [← cancel_epi S₁.homologyπ, homologyπ_naturality_assoc, hz,
      IsIso.hom_inv_id_assoc, comp_id]
  · rw [← cancel_epi S₂.homologyπ, reassoc_of% hz, CategoryTheory.ShortComplex.homologyπ_naturality,
      IsIso.inv_hom_id_assoc, comp_id]

