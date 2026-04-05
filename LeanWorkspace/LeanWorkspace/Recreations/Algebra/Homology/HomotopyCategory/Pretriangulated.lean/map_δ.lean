import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable (G : C ⥤ D) [G.Additive]

set_option backward.isDefEq.respectTransparency false in
theorem map_δ :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (CochainComplex.mappingCone.triangle φ).mor₃ ≫
      NatTrans.app ((Functor.mapHomologicalComplex G (ComplexShape.up ℤ)).commShiftIso 1).hom K =
    (mapHomologicalComplexIso φ G).hom ≫
      (CochainComplex.mappingCone.triangle ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).mor₃ := by
  ext n
  dsimp [mapHomologicalComplexIso]
  rw [mapHomologicalComplexXIso_eq φ G n (n + 1) rfl, mapHomologicalComplexXIso'_hom]
  simp only [Functor.mapHomologicalComplex_obj_X, add_comp, assoc, CochainComplex.mappingCone.inl_v_triangle_mor₃_f,
    shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    comp_neg, comp_id, CochainComplex.mappingCone.inr_f_triangle_mor₃_f, comp_zero, add_zero]
  dsimp [CochainComplex.mappingCone.triangle]
  rw [Cochain.rightShift_v _ 1 0 (by lia) n n (by lia) (n + 1) (by lia)]
  simp only [shiftFunctor_obj_X, Cochain.neg_v, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id, Functor.map_neg]

