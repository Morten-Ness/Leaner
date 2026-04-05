import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem mapRightHomologyIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (rightHomologyMap φ) ≫ (S₂.mapRightHomologyIso F).inv =
      (S₁.mapRightHomologyIso F).inv ≫ rightHomologyMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapRightHomologyIso F).hom, ← mapRightHomologyIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

