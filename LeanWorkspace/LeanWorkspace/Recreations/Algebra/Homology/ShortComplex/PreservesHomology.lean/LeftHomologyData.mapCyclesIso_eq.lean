import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem LeftHomologyData.mapCyclesIso_eq [S.HasLeftHomology]
    [F.PreservesLeftHomologyOf S] :
    S.mapCyclesIso F = (hl.map F).cyclesIso ≪≫ F.mapIso hl.cyclesIso.symm := by
  ext
  dsimp [CategoryTheory.ShortComplex.mapCyclesIso, cyclesIso]
  simp only [CategoryTheory.ShortComplex.LeftHomologyData.map_cyclesMap', ← cyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

