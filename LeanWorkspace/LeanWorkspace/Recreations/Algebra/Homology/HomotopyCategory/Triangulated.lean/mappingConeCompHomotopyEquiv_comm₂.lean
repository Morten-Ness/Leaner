import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeCompHomotopyEquiv_comm₂ :
    (CochainComplex.mappingConeCompHomotopyEquiv f g).hom ≫
      (triangle (CochainComplex.mappingConeCompTriangle f g).mor₁).mor₃ =
      (CochainComplex.mappingConeCompTriangle f g).mor₃ := by
  ext n
  simp [map, CochainComplex.mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom,
    lift_f _ _ _ _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

