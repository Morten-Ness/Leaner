import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem inl_v_triangle_mor₃_f (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq ≫ (CochainComplex.mappingCone.triangle φ).mor₃.f q =
      -(K.shiftFunctorObjXIso 1 q p (by rw [← hpq, neg_add_cancel_right])).inv := by
  dsimp [CochainComplex.mappingCone.triangle]
  -- the following list of lemmas was obtained by doing
  -- simp? [Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) p (by lia)]
  simp only [Int.reduceNeg, Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) p (by lia), shiftFunctor_obj_X,
    shiftFunctorObjXIso, Preadditive.comp_neg, inl_v_fst_v_assoc]

