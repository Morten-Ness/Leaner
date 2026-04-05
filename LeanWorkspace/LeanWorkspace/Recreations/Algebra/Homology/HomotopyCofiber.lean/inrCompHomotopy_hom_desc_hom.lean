import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable (α : G ⟶ K) (hα : Homotopy (φ ≫ α) 0)

theorem inrCompHomotopy_hom_desc_hom (hc : ∀ j, ∃ i, c.Rel i j) (i j : ι) :
    (HomologicalComplex.homotopyCofiber.inrCompHomotopy φ hc).hom i j ≫ (HomologicalComplex.homotopyCofiber.desc φ α hα).f j = hα.hom i j := by
  by_cases hij : c.Rel j i
  · dsimp
    simp only [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom φ hc i j hij, HomologicalComplex.homotopyCofiber.desc_f φ α hα _ _ hij,
      comp_add, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero]
  · simp only [Homotopy.zero _ _ _ hij, zero_comp]

