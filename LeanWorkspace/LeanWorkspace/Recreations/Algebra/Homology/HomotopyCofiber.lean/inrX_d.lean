import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem inrX_d (i j : ι) :
    HomologicalComplex.homotopyCofiber.inrX φ i ≫ HomologicalComplex.homotopyCofiber.d φ i j = G.d i j ≫ HomologicalComplex.homotopyCofiber.inrX φ j := by
  by_cases hij : c.Rel i j
  · by_cases hj : c.Rel j (c.next j)
    · apply HomologicalComplex.homotopyCofiber.ext_to_X _ _ _ hj
      · simp [HomologicalComplex.homotopyCofiber.d_fstX φ _ _ _ hij]
      · simp [HomologicalComplex.homotopyCofiber.d_sndX φ _ _ hij]
    · apply HomologicalComplex.homotopyCofiber.ext_to_X' _ _ hj
      simp [HomologicalComplex.homotopyCofiber.d_sndX φ _ _ hij]
  · rw [HomologicalComplex.homotopyCofiber.shape φ _ _ hij, G.shape _ _ hij, zero_comp, comp_zero]

