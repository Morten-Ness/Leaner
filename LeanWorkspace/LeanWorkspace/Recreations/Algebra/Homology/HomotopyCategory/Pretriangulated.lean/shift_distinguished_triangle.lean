import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem shift_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C) (n : ℤ) :
      (Triangle.shiftFunctor _ n).obj T ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C := by
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨Functor.mapIso _ e ≪≫ CochainComplex.mappingCone.shiftTrianglehIso φ n⟩⟩

