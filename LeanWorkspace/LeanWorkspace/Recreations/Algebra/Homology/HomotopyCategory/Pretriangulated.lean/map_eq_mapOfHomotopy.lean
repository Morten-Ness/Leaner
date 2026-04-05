import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)

variable (comm : φ₁ ≫ b = a ≫ φ₂)

theorem map_eq_mapOfHomotopy : CochainComplex.mappingCone.map φ₁ φ₂ a b comm = CochainComplex.mappingCone.mapOfHomotopy (Homotopy.ofEq comm) := by
  simp [CochainComplex.mappingCone.map, CochainComplex.mappingCone.mapOfHomotopy]

