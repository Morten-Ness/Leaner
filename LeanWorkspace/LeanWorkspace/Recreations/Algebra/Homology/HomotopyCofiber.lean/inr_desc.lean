import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

theorem inr_desc :
    HomologicalComplex.homotopyCofiber.inr φ ≫ HomologicalComplex.homotopyCofiber.desc φ α hα = α := by cat_disch

