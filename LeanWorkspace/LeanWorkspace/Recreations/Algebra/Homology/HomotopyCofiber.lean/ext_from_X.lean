import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem ext_from_X (i j : ι) (hij : c.Rel j i) {A : C} {f g : HomologicalComplex.homotopyCofiber.X φ j ⟶ A}
    (h₁ : HomologicalComplex.homotopyCofiber.inlX φ i j hij ≫ f = HomologicalComplex.homotopyCofiber.inlX φ i j hij ≫ g) (h₂ : HomologicalComplex.homotopyCofiber.inrX φ j ≫ f = HomologicalComplex.homotopyCofiber.inrX φ j ≫ g) :
    f = g := by
  haveI := HasHomotopyCofiber.hasBinaryBiproduct φ _ _ hij
  rw [← cancel_epi (HomologicalComplex.homotopyCofiber.XIsoBiprod φ j i hij).inv]
  apply biprod.hom_ext'
  · simpa [HomologicalComplex.homotopyCofiber.inlX] using h₁
  · obtain rfl := c.next_eq' hij
    simpa [HomologicalComplex.homotopyCofiber.inrX, dif_pos hij] using h₂

