import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem HomologyData.right_homologyIso_eq_left_homologyIso_trans_iso
    (h : S.HomologyData) [S.HasHomology] :
    h.right.homologyIso = h.left.homologyIso ≪≫ h.iso := by
  suffices h.iso = h.left.homologyIso.symm ≪≫ h.right.homologyIso by
    rw [this, Iso.self_symm_id_assoc]
  ext
  dsimp
  rw [← CategoryTheory.ShortComplex.leftRightHomologyComparison'_fac, leftRightHomologyComparison'_eq]

