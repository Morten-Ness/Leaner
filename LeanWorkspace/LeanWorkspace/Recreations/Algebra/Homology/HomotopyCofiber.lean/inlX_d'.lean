import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem inlX_d' (i j : ι) (hij : c.Rel i j) (hj : ¬ c.Rel j (c.next j)) :
    HomologicalComplex.homotopyCofiber.inlX φ j i hij ≫ HomologicalComplex.homotopyCofiber.d φ i j = φ.f j ≫ HomologicalComplex.homotopyCofiber.inrX φ j := by
  apply HomologicalComplex.homotopyCofiber.ext_to_X' _ _ hj
  simp [HomologicalComplex.homotopyCofiber.d_sndX φ i j hij]

