import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem mapCyclesIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (cyclesMap φ) ≫ (S₂.mapCyclesIso F).inv =
      (S₁.mapCyclesIso F).inv ≫ cyclesMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapCyclesIso F).hom, ← mapCyclesIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

