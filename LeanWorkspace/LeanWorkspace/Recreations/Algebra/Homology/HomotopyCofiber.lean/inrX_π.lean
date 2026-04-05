import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

theorem inrX_π (i : ι) :
    HomologicalComplex.homotopyCofiber.inrX K i ≫ (HomologicalComplex.cylinder.π K).f i = (biprod.desc (𝟙 _) (𝟙 K)).f i := HomologicalComplex.homotopyCofiber.inrX_desc_f HomologicalComplex.homotopyCofiber _ _ _ _

