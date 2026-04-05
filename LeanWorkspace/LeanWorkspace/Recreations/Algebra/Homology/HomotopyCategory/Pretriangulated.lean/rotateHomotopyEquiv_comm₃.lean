import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem rotateHomotopyEquiv_comm₃ :
    (CochainComplex.mappingCone.rotateHomotopyEquiv φ).hom ≫ (CochainComplex.mappingCone.triangle (inr φ)).mor₃ = -φ⟦1⟧' := by
  ext p
  dsimp [CochainComplex.mappingCone.rotateHomotopyEquiv]
  -- the following list of lemmas has been obtained by doing
  -- simp? [lift_f _ _ _ _ _ (p + 1) rfl,
  --   (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by lia)]
  simp only [Int.reduceNeg, lift_f _ _ _ _ _ (p + 1) rfl, shiftFunctor_obj_X', Cocycle.coe_neg,
    Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.neg_v,
    (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by lia),
    shiftFunctor_obj_X, mul_one, sub_self, mul_zero, Int.zero_ediv, add_zero, Int.negOnePow_one,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Cochain.ofHom_v, id_comp,
    Units.neg_smul, one_smul, neg_neg, Preadditive.neg_comp, Preadditive.add_comp, assoc,
    CochainComplex.mappingCone.inl_v_triangle_mor₃_f, Iso.refl_inv, Preadditive.comp_neg, comp_id, CochainComplex.mappingCone.inr_f_triangle_mor₃_f,
    comp_zero, neg_zero]

