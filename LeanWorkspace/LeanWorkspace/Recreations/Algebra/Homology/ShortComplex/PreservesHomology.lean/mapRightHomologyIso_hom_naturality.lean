import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem mapRightHomologyIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    rightHomologyMap (F.mapShortComplex.map φ) ≫ (S₂.mapRightHomologyIso F).hom =
      (S₁.mapRightHomologyIso F).hom ≫ F.map (rightHomologyMap φ) := by
  dsimp only [rightHomologyMap, CategoryTheory.ShortComplex.mapRightHomologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', Iso.refl]
  simp only [RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    ← rightHomologyMap'_comp, comp_id, id_comp]

