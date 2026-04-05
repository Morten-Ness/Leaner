import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem RightHomologyData.mapOpcyclesIso_eq [S.HasRightHomology]
    [F.PreservesRightHomologyOf S] :
    S.mapOpcyclesIso F = (hr.map F).opcyclesIso ≪≫ F.mapIso hr.opcyclesIso.symm := by
  ext
  dsimp [CategoryTheory.ShortComplex.mapOpcyclesIso, opcyclesIso]
  simp only [CategoryTheory.ShortComplex.RightHomologyData.map_opcyclesMap', ← opcyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

