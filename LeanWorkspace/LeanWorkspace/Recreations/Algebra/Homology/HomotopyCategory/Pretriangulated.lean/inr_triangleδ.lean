import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem inr_triangleδ : inr φ ≫ (CochainComplex.mappingCone.triangle φ).mor₃ = 0 := by ext; simp

