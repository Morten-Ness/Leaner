import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeCompTriangle_mor₃_naturality {Y₁ Y₂ Y₃ : CochainComplex C ℤ} (f' : Y₁ ⟶ Y₂)
    (g' : Y₂ ⟶ Y₃) (φ : mk₂ f g ⟶ mk₂ f' g') :
    map g g' (φ.app 1) (φ.app 2) (naturality' φ 1 2) ≫ (CochainComplex.mappingConeCompTriangle f' g').mor₃ =
      (CochainComplex.mappingConeCompTriangle f g).mor₃ ≫
        (map f f' (φ.app 0) (φ.app 1) (naturality' φ 0 1))⟦1⟧' := by
  ext n
  dsimp [map]
  -- the following list of lemmas was obtained by doing simp? [ext_from_iff _ (n + 1) _ rfl]
  simp only [Int.reduceNeg, Fin.isValue, assoc, inr_f_desc_f, HomologicalComplex.comp_f,
    ext_from_iff _ (n + 1) _ rfl, inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    inl_v_triangle_mor₃_f_assoc, triangle_obj₁, shiftFunctor_obj_X', shiftFunctor_obj_X,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Preadditive.neg_comp,
    id_comp, Preadditive.comp_neg, inr_f_desc_f_assoc, inr_f_triangle_mor₃_f_assoc, zero_comp,
    comp_zero, and_self]

