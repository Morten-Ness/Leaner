import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem mapOpcyclesIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (opcyclesMap φ) ≫ (S₂.mapOpcyclesIso F).inv =
      (S₁.mapOpcyclesIso F).inv ≫ opcyclesMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapOpcyclesIso F).hom, ← mapOpcyclesIso_hom_naturality_assoc,
    Iso.hom_inv_id, comp_id, Iso.hom_inv_id_assoc]

