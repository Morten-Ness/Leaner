import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

theorem eq_desc (f : HomologicalComplex.homotopyCofiber φ ⟶ K) (hc : ∀ j, ∃ i, c.Rel i j) :
    f = HomologicalComplex.homotopyCofiber.desc φ (HomologicalComplex.homotopyCofiber.inr φ ≫ f) (Homotopy.trans (Homotopy.ofEq (by simp))
      (((HomologicalComplex.homotopyCofiber.inrCompHomotopy φ hc).compRight f).trans (Homotopy.ofEq (by simp)))) := by
  ext j
  by_cases hj : c.Rel j (c.next j)
  · apply HomologicalComplex.homotopyCofiber.ext_from_X φ _ _ hj
    · simp [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ _ _ hj]
    · simp
  · apply HomologicalComplex.homotopyCofiber.ext_from_X' φ _ hj
    simp

