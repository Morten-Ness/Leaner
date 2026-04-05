import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

theorem desc_f' (j : ι) (hj : ¬ c.Rel j (c.next j)) :
    (HomologicalComplex.homotopyCofiber.desc φ α hα).f j = HomologicalComplex.homotopyCofiber.sndX φ j ≫ α.f j := by
  apply dif_neg hj

