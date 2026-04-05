import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeCompHomotopyEquiv_hom_inv_id :
    (CochainComplex.mappingConeCompHomotopyEquiv f g).hom ≫
      (CochainComplex.mappingConeCompHomotopyEquiv f g).inv = 𝟙 _ := by
  simp [CochainComplex.mappingConeCompHomotopyEquiv]

