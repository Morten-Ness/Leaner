import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem d_sndX (i j : ι) (hij : c.Rel i j) :
    HomologicalComplex.homotopyCofiber.d φ i j ≫ HomologicalComplex.homotopyCofiber.sndX φ j = HomologicalComplex.homotopyCofiber.fstX φ i j hij ≫ φ.f j + HomologicalComplex.homotopyCofiber.sndX φ i ≫ G.d i j := by
  dsimp [HomologicalComplex.homotopyCofiber.d]
  split_ifs with hij <;> simp

