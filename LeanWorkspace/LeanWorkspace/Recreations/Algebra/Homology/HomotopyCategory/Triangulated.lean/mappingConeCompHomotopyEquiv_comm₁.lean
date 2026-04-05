import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

theorem mappingConeCompHomotopyEquiv_comm₁ :
    inr (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp])) ≫
      (CochainComplex.mappingConeCompHomotopyEquiv f g).inv = (CochainComplex.mappingConeCompTriangle f g).mor₂ := by
  simp [map, CochainComplex.mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv]

