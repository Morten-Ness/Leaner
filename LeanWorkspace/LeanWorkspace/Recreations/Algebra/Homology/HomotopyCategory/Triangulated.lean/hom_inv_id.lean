import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

set_option backward.isDefEq.respectTransparency false in
theorem hom_inv_id : CochainComplex.MappingConeCompHomotopyEquiv.hom f g ≫ CochainComplex.MappingConeCompHomotopyEquiv.inv f g = 𝟙 _ := by
  ext n
  simp [CochainComplex.MappingConeCompHomotopyEquiv.hom, CochainComplex.MappingConeCompHomotopyEquiv.inv, lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

