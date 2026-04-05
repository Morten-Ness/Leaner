import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem isomorphic_distinguished (T₁ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT₁ : T₁ ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C) (T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (e : T₂ ≅ T₁) : T₂ ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C := by
  obtain ⟨X, Y, f, ⟨e'⟩⟩ := hT₁
  exact ⟨X, Y, f, ⟨e ≪≫ e'⟩⟩

