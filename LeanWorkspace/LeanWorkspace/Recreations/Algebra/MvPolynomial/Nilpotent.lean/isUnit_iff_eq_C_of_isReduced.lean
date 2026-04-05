import Mathlib

variable {σ R : Type*} [CommRing R] {P : MvPolynomial σ R}

private theorem isNilpotent_iff_of_fintype [Finite σ] :
    IsNilpotent P ↔ ∀ i, IsNilpotent (P.coeff i) := by
  classical
  -- Note: including `Fintype.ofFinite σ` in the entire context interferes with the `rw` below.
  refine have := Fintype.ofFinite σ; Fintype.induction_empty_option ?_ ?_ ?_ σ P
  · intro α β _ e h₁ P
    rw [← IsNilpotent.map_iff (rename_injective _ e.symm.injective), h₁,
      (Finsupp.equivCongrLeft e).forall_congr_left]
    simp [Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective]
  · simp [Unique.forall_iff, ← IsNilpotent.map_iff (isEmptyRingEquiv R PEmpty).injective,
      -isEmptyRingEquiv_apply, isEmptyRingEquiv_eq_coeff_zero]
  · intro α _ H P
    obtain ⟨P, rfl⟩ := (optionEquivLeft _ _).symm.surjective P
    simp [IsNilpotent.map_iff (optionEquivLeft _ _).symm.injective,
      Polynomial.isNilpotent_iff, H, Finsupp.optionEquiv.forall_congr_left,
      ← optionEquivLeft_coeff_some_coeff_none, Finsupp.coe_update]


theorem isUnit_iff_eq_C_of_isReduced [IsReduced R] :
    IsUnit P ↔ ∃ r, IsUnit r ∧ P = C r := by
  rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced, totalDegree_eq_zero_iff_eq_C]
  refine ⟨fun H ↦ ⟨_, H⟩, ?_⟩
  rintro ⟨r, hr, rfl⟩
  simpa

