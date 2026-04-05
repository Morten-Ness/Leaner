import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem inlX_sndX (i j : ι) (hij : c.Rel j i) :
    HomologicalComplex.homotopyCofiber.inlX φ i j hij ≫ HomologicalComplex.homotopyCofiber.sndX φ j = 0 := by
  obtain rfl := c.next_eq' hij
  simp [HomologicalComplex.homotopyCofiber.inlX, HomologicalComplex.homotopyCofiber.sndX, dif_pos hij]

