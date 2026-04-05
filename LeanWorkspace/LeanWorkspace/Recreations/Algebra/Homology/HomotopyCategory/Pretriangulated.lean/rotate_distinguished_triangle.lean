import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem rotate_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    T ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C ↔ T.rotate ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C := by
  constructor
  · exact HomotopyCategory.Pretriangulated.rotate_distinguished_triangle' T
  · intro hT
    exact HomotopyCategory.Pretriangulated.isomorphic_distinguished _ (HomotopyCategory.Pretriangulated.invRotate_distinguished_triangle' T.rotate hT) _
      ((triangleRotation _).unitIso.app T)

