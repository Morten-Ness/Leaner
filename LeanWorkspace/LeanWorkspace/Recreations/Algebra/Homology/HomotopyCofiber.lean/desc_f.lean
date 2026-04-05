import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

theorem desc_f (j k : ι) (hjk : c.Rel j k) :
    (HomologicalComplex.homotopyCofiber.desc φ α hα).f j = HomologicalComplex.homotopyCofiber.fstX φ j _ hjk ≫ hα.hom _ j + HomologicalComplex.homotopyCofiber.sndX φ j ≫ α.f j := by
  obtain rfl := c.next_eq' hjk
  apply dif_pos hjk

