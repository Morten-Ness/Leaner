import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

theorem mapCyclesIso_hom_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).hom ≫ F.map S.iCycles = (S.map F).iCycles := by
  apply LeftHomologyData.cyclesIso_hom_comp_i

