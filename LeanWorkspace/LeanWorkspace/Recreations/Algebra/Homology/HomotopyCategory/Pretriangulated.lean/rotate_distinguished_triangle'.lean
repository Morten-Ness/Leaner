import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem rotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C) : T.rotate ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C := by
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨(rotate _).mapIso e ≪≫ CochainComplex.mappingCone.rotateTrianglehIso φ⟩⟩

