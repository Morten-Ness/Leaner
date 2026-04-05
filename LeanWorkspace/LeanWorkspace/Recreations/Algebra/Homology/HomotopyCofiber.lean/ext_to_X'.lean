import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem ext_to_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : A ⟶ HomologicalComplex.homotopyCofiber.X φ i}
    (h : f ≫ HomologicalComplex.homotopyCofiber.sndX φ i = g ≫ HomologicalComplex.homotopyCofiber.sndX φ i) : f = g := by
  rw [← cancel_mono (HomologicalComplex.homotopyCofiber.XIso φ i hi).hom]
  simpa only [HomologicalComplex.homotopyCofiber.sndX, dif_neg hi] using h

