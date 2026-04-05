import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

theorem isIso_cyclesMap'_of_isIso_of_mono (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (CategoryTheory.ShortComplex.cyclesMap' φ h₁ h₂) := by
  refine ⟨h₁.liftK (h₂.i ≫ inv φ.τ₂) ?_, ?_, ?_⟩
  · simp only [assoc, ← cancel_mono φ.τ₃, zero_comp, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, h₂.wi]
  · simp only [← cancel_mono h₁.i, assoc, CategoryTheory.ShortComplex.LeftHomologyData.liftK_i h₁, cyclesMap'_i_assoc,
      IsIso.hom_inv_id, comp_id, id_comp]
  · simp only [← cancel_mono h₂.i, assoc, CategoryTheory.ShortComplex.cyclesMap'_i, h₁.liftK_i_assoc,
      IsIso.inv_hom_id, comp_id, id_comp]

