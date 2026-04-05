import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem sndX_inrX (i : ι) (hi : ¬ c.Rel i (c.next i)) :
    HomologicalComplex.homotopyCofiber.sndX φ i ≫ HomologicalComplex.homotopyCofiber.inrX φ i = 𝟙 _ := by
  dsimp [HomologicalComplex.homotopyCofiber.sndX, HomologicalComplex.homotopyCofiber.inrX]
  simp only [dif_neg hi, Iso.hom_inv_id]

