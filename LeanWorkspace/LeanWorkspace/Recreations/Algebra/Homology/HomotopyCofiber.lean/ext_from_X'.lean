import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem ext_from_X' (i : ι) (hi : ¬ c.Rel i (c.next i)) {A : C} {f g : HomologicalComplex.homotopyCofiber.X φ i ⟶ A}
    (h : HomologicalComplex.homotopyCofiber.inrX φ i ≫ f = HomologicalComplex.homotopyCofiber.inrX φ i ≫ g) : f = g := by
  rw [← cancel_epi (HomologicalComplex.homotopyCofiber.XIso φ i hi).inv]
  simpa only [HomologicalComplex.homotopyCofiber.inrX, dif_neg hi] using h

