import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

variable (hc : ∀ j, ∃ i, c.Rel i j)

set_option backward.isDefEq.respectTransparency false in
theorem inlX_nullHomotopy_f (i j : ι) (hij : c.Rel j i) :
    HomologicalComplex.homotopyCofiber.inlX K i j hij ≫ (HomologicalComplex.cylinder.πCompι₀Homotopy.nullHomotopicMap K).f j =
      HomologicalComplex.homotopyCofiber.inlX K i j hij ≫ (HomologicalComplex.cylinder.π K ≫ HomologicalComplex.cylinder.ι₀ K - 𝟙 _).f j := by
  dsimp [HomologicalComplex.cylinder.πCompι₀Homotopy.nullHomotopicMap]
  by_cases! hj : ∃ (k : ι), c.Rel k j
  · obtain ⟨k, hjk⟩ := hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f hjk hij, homotopyCofiber_X, homotopyCofiber_d,
      HomologicalComplex.homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, HomologicalComplex.homotopyCofiber.inlX_fstX_assoc,
      HomologicalComplex.homotopyCofiber.inlX_sndX_assoc, zero_comp, add_zero, comp_sub, inlX_π_assoc, comp_id,
      zero_sub, ← HomologicalComplex.comp_f_assoc, biprod.lift_snd, neg_f_apply, id_f,
      neg_comp, id_comp]
  · simp only [Homotopy.nullHomotopicMap'_f_of_not_rel_right hij hj,
      homotopyCofiber_X, homotopyCofiber_d, assoc, comp_sub, comp_id,
      HomologicalComplex.homotopyCofiber.d_sndX_assoc _ _ _ hij, add_comp, comp_add, zero_comp, add_zero,
      HomologicalComplex.homotopyCofiber.inlX_fstX_assoc, HomologicalComplex.homotopyCofiber.inlX_sndX_assoc,
      ← HomologicalComplex.comp_f_assoc, biprod.lift_snd, neg_f_apply, id_f, neg_comp,
      id_comp, inlX_π_assoc, zero_sub]

include hc

