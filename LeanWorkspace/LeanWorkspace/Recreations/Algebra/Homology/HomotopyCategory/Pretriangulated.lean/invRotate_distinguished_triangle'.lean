import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem invRotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C) : T.invRotate ∈ HomotopyCategory.Pretriangulated.distinguishedTriangles C := HomotopyCategory.Pretriangulated.isomorphic_distinguished _
    (HomotopyCategory.Pretriangulated.shift_distinguished_triangle _ (HomotopyCategory.Pretriangulated.rotate_distinguished_triangle' _
      (HomotopyCategory.Pretriangulated.rotate_distinguished_triangle' _ hT)) _) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

