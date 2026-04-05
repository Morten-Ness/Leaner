import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem RightHomologyData.mapRightHomologyIso_eq [S.HasRightHomology]
    [F.PreservesRightHomologyOf S] :
    S.mapRightHomologyIso F = (hr.map F).rightHomologyIso ≪≫
      F.mapIso hr.rightHomologyIso.symm := by
  ext
  dsimp [CategoryTheory.ShortComplex.mapRightHomologyIso, rightHomologyIso]
  simp only [CategoryTheory.ShortComplex.RightHomologyData.map_rightHomologyMap', ← rightHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

