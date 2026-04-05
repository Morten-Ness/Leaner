import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem inrX_sndX (i : ι) : HomologicalComplex.homotopyCofiber.inrX φ i ≫ HomologicalComplex.homotopyCofiber.sndX φ i = 𝟙 _ := by
  dsimp [HomologicalComplex.homotopyCofiber.sndX, HomologicalComplex.homotopyCofiber.inrX]
  split_ifs with hi <;> simp

