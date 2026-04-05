import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

set_option backward.isDefEq.respectTransparency false in
theorem triangleMapOfHomotopy_comm₃ :
    CochainComplex.mappingCone.mapOfHomotopy H ≫ (CochainComplex.mappingCone.triangle φ₂).mor₃ = (CochainComplex.mappingCone.triangle φ₁).mor₃ ≫ a⟦1⟧' := by
  ext p
  dsimp [CochainComplex.mappingCone.mapOfHomotopy, CochainComplex.mappingCone.triangle]
  -- the following list of lemmas as been obtained by doing
  -- simp? [ext_from_iff _ _ _ rfl, Cochain.rightShift_v _ 1 0 _ p p _ (p + 1) rfl]
  simp only [Int.reduceNeg, Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 _ p p _ (p + 1) rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id, Preadditive.comp_neg,
    Preadditive.neg_comp, ext_from_iff _ _ _ rfl, inl_v_desc_f_assoc, Cochain.add_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v, Preadditive.add_comp,
    assoc, inl_v_fst_v, inr_f_fst_v, comp_zero, add_zero, inl_v_fst_v_assoc, inr_f_desc_f_assoc,
    HomologicalComplex.comp_f, neg_zero, inr_f_fst_v_assoc, zero_comp, and_self]

