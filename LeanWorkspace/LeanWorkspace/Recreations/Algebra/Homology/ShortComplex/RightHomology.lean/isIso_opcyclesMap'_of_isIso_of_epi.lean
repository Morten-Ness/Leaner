import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

theorem isIso_opcyclesMap'_of_isIso_of_epi (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₁ : Epi φ.τ₁)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (CategoryTheory.ShortComplex.opcyclesMap' φ h₁ h₂) := by
  refine ⟨h₂.descQ (inv φ.τ₂ ≫ h₁.p) ?_, ?_, ?_⟩
  · simp only [← cancel_epi φ.τ₁, comp_zero, φ.comm₁₂_assoc, IsIso.hom_inv_id_assoc, h₁.wp]
  · simp only [← cancel_epi h₁.p, p_opcyclesMap'_assoc, CategoryTheory.ShortComplex.RightHomologyData.p_descQ h₂,
      IsIso.hom_inv_id_assoc, comp_id]
  · simp only [← cancel_epi h₂.p, h₂.p_descQ_assoc, assoc, CategoryTheory.ShortComplex.p_opcyclesMap',
      IsIso.inv_hom_id_assoc, comp_id]

