import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem inr_f_triangle_mor₃_f (p : ℤ) : (inr φ).f p ≫ (CochainComplex.mappingCone.triangle φ).mor₃.f p = 0 := by
  dsimp [CochainComplex.mappingCone.triangle]
  -- the following list of lemmas was obtained by doing
  -- simp? [Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p+1) rfl]
  simp only [Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p + 1) rfl, shiftFunctor_obj_X,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id,
    Preadditive.comp_neg, inr_f_fst_v, neg_zero]

