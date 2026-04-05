import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem HomologyData.left_homologyIso_eq_right_homologyIso_trans_iso_symm
    (h : S.HomologyData) [S.HasHomology] :
    h.left.homologyIso = h.right.homologyIso ≪≫ h.iso.symm := by
  rw [right_homologyIso_eq_left_homologyIso_trans_iso]
  cat_disch

