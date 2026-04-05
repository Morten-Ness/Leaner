import Mathlib

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

theorem rotateHomotopyEquiv_comm₂ :
    (HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.triangle φ).mor₃ ≫
      (HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.rotateHomotopyEquiv φ).hom =
      (HomotopyCategory.quotient _ _).map (inr (inr φ)) := by
  simpa only [Functor.map_comp]
    using HomotopyCategory.eq_of_homotopy _ _ (CochainComplex.mappingCone.rotateHomotopyEquivComm₂Homotopy φ)

