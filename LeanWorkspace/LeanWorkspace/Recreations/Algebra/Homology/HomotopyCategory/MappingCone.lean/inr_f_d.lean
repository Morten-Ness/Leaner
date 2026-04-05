import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem inr_f_d (n₁ n₂ : ℤ) :
    (CochainComplex.mappingCone.inr φ).f n₁ ≫ (CochainComplex.mappingCone φ).d n₁ n₂ = G.d n₁ n₂ ≫ (CochainComplex.mappingCone.inr φ).f n₂ := by
  simp

