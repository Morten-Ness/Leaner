import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable (H : C ⥤ D) [H.Additive]
  [HasHomotopyCofiber ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)]

set_option backward.isDefEq.respectTransparency false in
theorem map_inr :
    (H.mapHomologicalComplex (ComplexShape.up ℤ)).map (CochainComplex.mappingCone.inr φ) ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso φ H).hom =
    CochainComplex.mappingCone.inr ((Functor.mapHomologicalComplex H (ComplexShape.up ℤ)).map φ) := by
  ext n
  dsimp [CochainComplex.mappingCone.mapHomologicalComplexIso]
  simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso_eq φ H n (n + 1) rfl, CochainComplex.mappingCone.ext_to_iff CochainComplex.mappingCone _ _ _ rfl,
    Functor.mapHomologicalComplex_obj_X, mapHomologicalComplexXIso'_hom, comp_add,
    add_comp, assoc, CochainComplex.mappingCone.inl_v_fst_v, comp_id, CochainComplex.mappingCone.inr_f_fst_v, comp_zero, add_zero, CochainComplex.mappingCone.inl_v_snd_v,
    CochainComplex.mappingCone.inr_f_snd_v, zero_add, ← H.map_comp, H.map_zero, H.map_id, and_self]

