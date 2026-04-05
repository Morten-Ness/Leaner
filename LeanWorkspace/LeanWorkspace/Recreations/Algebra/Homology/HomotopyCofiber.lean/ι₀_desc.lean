import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

variable (φ₀ φ₁ : K ⟶ F) (h : Homotopy φ₀ φ₁)

theorem ι₀_desc : HomologicalComplex.cylinder.ι₀ K ≫ HomologicalComplex.cylinder.desc φ₀ φ₁ h = φ₀ := by simp [HomologicalComplex.cylinder.ι₀, HomologicalComplex.cylinder.desc]

