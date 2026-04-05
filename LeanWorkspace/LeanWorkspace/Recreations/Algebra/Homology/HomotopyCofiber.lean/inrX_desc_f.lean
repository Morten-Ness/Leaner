import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

theorem inrX_desc_f (i : ι) :
    HomologicalComplex.homotopyCofiber.inrX φ i ≫ (HomologicalComplex.homotopyCofiber.desc φ α hα).f i = α.f i := by
  dsimp [HomologicalComplex.homotopyCofiber.desc]
  split_ifs <;> simp

