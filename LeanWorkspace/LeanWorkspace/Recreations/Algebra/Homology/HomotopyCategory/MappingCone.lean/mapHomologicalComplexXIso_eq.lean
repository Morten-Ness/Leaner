import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable (H : C ⥤ D) [H.Additive]
  [HasHomotopyCofiber ((H.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)]

theorem mapHomologicalComplexXIso_eq (n m : ℤ) (hnm : n + 1 = m) :
    CochainComplex.mappingCone.mapHomologicalComplexXIso φ H n = CochainComplex.mappingCone.mapHomologicalComplexXIso' φ H n m hnm := by
  subst hnm
  rfl

