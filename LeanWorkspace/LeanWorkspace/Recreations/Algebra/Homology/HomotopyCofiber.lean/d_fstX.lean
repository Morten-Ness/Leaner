import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem d_fstX (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    HomologicalComplex.homotopyCofiber.d φ i j ≫ HomologicalComplex.homotopyCofiber.fstX φ j k hjk = -HomologicalComplex.homotopyCofiber.fstX φ i j hij ≫ F.d j k := by
  obtain rfl := c.next_eq' hjk
  simp [HomologicalComplex.homotopyCofiber.d, dif_pos hij, dif_pos hjk]

