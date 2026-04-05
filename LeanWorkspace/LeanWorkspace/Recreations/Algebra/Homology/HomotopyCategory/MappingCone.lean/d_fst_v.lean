import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem d_fst_v (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (CochainComplex.mappingCone φ).d i j ≫ (CochainComplex.mappingCone.fst φ).1.v j k hjk =
      -(CochainComplex.mappingCone.fst φ).1.v i j hij ≫ F.d j k := by
  apply homotopyCofiber.d_fstX

