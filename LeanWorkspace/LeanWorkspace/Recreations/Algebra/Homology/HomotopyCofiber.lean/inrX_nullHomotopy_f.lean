import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

variable (hc : ∀ j, ∃ i, c.Rel i j)

set_option backward.isDefEq.respectTransparency false in
theorem inrX_nullHomotopy_f (j : ι) :
    HomologicalComplex.homotopyCofiber.inrX K j ≫ (HomologicalComplex.cylinder.πCompι₀Homotopy.nullHomotopicMap K).f j = HomologicalComplex.homotopyCofiber.inrX K j ≫ (HomologicalComplex.cylinder.π K ≫ HomologicalComplex.cylinder.ι₀ K - 𝟙 _).f j := by
  have : biprod.lift (𝟙 K) (-𝟙 K) = biprod.inl - biprod.inr :=
    biprod.hom_ext _ _ (by simp) (by simp)
  obtain ⟨i, hij⟩ := hc j
  dsimp [HomologicalComplex.cylinder.πCompι₀Homotopy.nullHomotopicMap]
  by_cases hj : ∃ (k : ι), c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    simp only [Homotopy.nullHomotopicMap'_f hij hjk,
      homotopyCofiber_X, homotopyCofiber_d, assoc, comp_add,
      HomologicalComplex.homotopyCofiber.inrX_d_assoc, HomologicalComplex.homotopyCofiber.inrX_sndX_assoc, comp_sub,
      inrX_π_assoc, comp_id, ← Hom.comm_assoc, HomologicalComplex.homotopyCofiber.inlX_d HomologicalComplex.homotopyCofiber _ _ _ _ _ hjk,
      comp_neg, add_neg_cancel_left]
    rw [← cancel_epi (biprodXIso K K j).inv]
    ext
    · simp [HomologicalComplex.cylinder.ι₀]
    · dsimp
      simp only [inr_biprodXIso_inv_assoc, biprod_inr_snd_f_assoc, comp_sub,
        biprod_inr_desc_f_assoc, id_f, id_comp, HomologicalComplex.cylinder.ι₀, comp_f, this,
        sub_f_apply, sub_comp, homotopyCofiber_X, HomologicalComplex.homotopyCofiber.inr_f]
  · simp only [not_exists] at hj
    simp only [assoc, Homotopy.nullHomotopicMap'_f_of_not_rel_left hij hj, homotopyCofiber_X,
      homotopyCofiber_d, HomologicalComplex.homotopyCofiber.inlX_d' HomologicalComplex.homotopyCofiber _ _ _ _ (hj _), HomologicalComplex.homotopyCofiber.inrX_sndX_assoc,
      comp_sub, inrX_π_assoc, comp_id, HomologicalComplex.cylinder.ι₀, comp_f, HomologicalComplex.homotopyCofiber.inr_f]
    rw [← cancel_epi (biprodXIso K K j).inv]
    ext
    · simp
    · simp [this]

