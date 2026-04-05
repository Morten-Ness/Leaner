import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem inrX_fstX (i j : ι) (hij : c.Rel i j) :
    HomologicalComplex.homotopyCofiber.inrX φ i ≫ HomologicalComplex.homotopyCofiber.fstX φ i j hij = 0 := by
  obtain rfl := c.next_eq' hij
  simp [HomologicalComplex.homotopyCofiber.inrX, HomologicalComplex.homotopyCofiber.fstX, dif_pos hij]

