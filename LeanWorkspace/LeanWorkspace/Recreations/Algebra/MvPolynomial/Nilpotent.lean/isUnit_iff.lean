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


theorem isUnit_iff : IsUnit P ↔ IsUnit (P.coeff 0) ∧ ∀ i ≠ 0, IsNilpotent (P.coeff i) := by
  classical
  refine ⟨fun H ↦ ⟨H.map constantCoeff, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · intro n hn
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by simpa [Finsupp.ext_iff] using hn
    let e := (optionEquivLeft _ _).symm.trans (renameEquiv R (Equiv.optionSubtypeNe i))
    have H := (Polynomial.coeff_isUnit_isNilpotent_of_isUnit (H.map e.symm)).2 (n i) hi
    simp only [ne_eq, MvPolynomial.isNilpotent_iff] at H
    convert ← H (n.equivMapDomain (Equiv.optionSubtypeNe i).symm).some
    refine (optionEquivLeft_coeff_some_coeff_none _ _ _ _).trans ?_
    simp [Finsupp.equivMapDomain_eq_mapDomain,
      coeff_rename_mapDomain _ (Equiv.optionSubtypeNe i).symm.injective]
  · have : IsNilpotent (P - C (P.coeff 0)) := by
      simp +contextual [MvPolynomial.isNilpotent_iff, apply_ite, eq_comm, h₂]
    simpa using this.isUnit_add_right_of_commute (h₁.map C) (.all _ _)

