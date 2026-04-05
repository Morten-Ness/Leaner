import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem inlX_d (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    HomologicalComplex.homotopyCofiber.inlX φ j i hij ≫ HomologicalComplex.homotopyCofiber.d φ i j = -F.d j k ≫ HomologicalComplex.homotopyCofiber.inlX φ k j hjk + φ.f j ≫ HomologicalComplex.homotopyCofiber.inrX φ j := by
  apply HomologicalComplex.homotopyCofiber.ext_to_X φ j k hjk
  · simp [HomologicalComplex.homotopyCofiber.d_fstX φ _ _ _ hij hjk]
  · simp [HomologicalComplex.homotopyCofiber.d_sndX φ _ _ hij]

