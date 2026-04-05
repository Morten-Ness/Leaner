import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem d_fst_v' (i j : ℤ) (hij : i + 1 = j) :
    (CochainComplex.mappingCone φ).d (i - 1) i ≫ (CochainComplex.mappingCone.fst φ).1.v i j hij =
      -(CochainComplex.mappingCone.fst φ).1.v (i - 1) i (by lia) ≫ F.d i j := CochainComplex.mappingCone.d_fst_v φ (i - 1) i j (by lia) hij

