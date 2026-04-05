import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

theorem inlX_π (i j : ι) (hij : c.Rel j i) :
    HomologicalComplex.homotopyCofiber.inlX K i j hij ≫ (HomologicalComplex.cylinder.π K).f j = 0 := by
  simp [HomologicalComplex.cylinder.π, HomologicalComplex.cylinder.desc, Homotopy.equivSubZero]

