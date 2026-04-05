import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
theorem mapOpcyclesIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    opcyclesMap (F.mapShortComplex.map φ) ≫ (S₂.mapOpcyclesIso F).hom =
      (S₁.mapOpcyclesIso F).hom ≫ F.map (opcyclesMap φ) := by
  dsimp only [opcyclesMap, CategoryTheory.ShortComplex.mapOpcyclesIso, RightHomologyData.opcyclesIso,
    opcyclesMapIso', Iso.refl]
  simp only [RightHomologyData.map_opcyclesMap', Functor.mapShortComplex_obj, ← opcyclesMap'_comp,
    comp_id, id_comp]

