import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

theorem inlX_desc_f (i j : ι) (hjk : c.Rel j i) :
    HomologicalComplex.homotopyCofiber.inlX φ i j hjk ≫ (HomologicalComplex.homotopyCofiber.desc φ α hα).f j = hα.hom i j := by
  obtain rfl := c.next_eq' hjk
  dsimp [HomologicalComplex.homotopyCofiber.desc]
  rw [dif_pos hjk, comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]

