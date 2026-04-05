import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem ext_to_X (i j : ι) (hij : c.Rel i j) {A : C} {f g : A ⟶ HomologicalComplex.homotopyCofiber.X φ i}
    (h₁ : f ≫ HomologicalComplex.homotopyCofiber.fstX φ i j hij = g ≫ HomologicalComplex.homotopyCofiber.fstX φ i j hij) (h₂ : f ≫ HomologicalComplex.homotopyCofiber.sndX φ i = g ≫ HomologicalComplex.homotopyCofiber.sndX φ i) :
    f = g := by
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_mono (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i j hij).hom]
  apply biprod.hom_ext
  · simpa using h₁
  · obtain rfl := c.next_eq' hij
    simpa [HomologicalComplex.homotopyCofiber.sndX, dif_pos hij] using h₂

