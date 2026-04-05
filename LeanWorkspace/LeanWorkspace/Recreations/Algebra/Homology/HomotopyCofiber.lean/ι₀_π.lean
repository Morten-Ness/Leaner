import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

theorem ι₀_π : HomologicalComplex.cylinder.ι₀ K ≫ HomologicalComplex.cylinder.π K = 𝟙 K := by simp [HomologicalComplex.cylinder.π]

