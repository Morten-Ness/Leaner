import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C]

variable (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C _ n)).Splitting)

variable [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃ :
    (CochainComplex.mappingConeHomOfDegreewiseSplitIso S σ).inv ≫
      (mappingCone.triangle (CochainComplex.homOfDegreewiseSplit S σ)).mor₃ = -S.g⟦(1 : ℤ)⟧' := by
  ext n
  dsimp [CochainComplex.mappingConeHomOfDegreewiseSplitXIso]
  simp only [Int.reduceNeg, id_comp, sub_comp, assoc, mappingCone.inl_v_triangle_mor₃_f,
    shiftFunctor_obj_X, shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_inv, comp_neg, comp_id,
    mappingCone.inr_f_triangle_mor₃_f, comp_zero, sub_zero]

