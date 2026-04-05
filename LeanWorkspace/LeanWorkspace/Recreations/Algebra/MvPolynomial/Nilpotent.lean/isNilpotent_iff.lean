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


theorem isNilpotent_iff : IsNilpotent P ↔ ∀ i, IsNilpotent (P.coeff i) := by
  obtain ⟨n, f, hf, P, rfl⟩ := P.exists_fin_rename
  rw [IsNilpotent.map_iff (rename_injective _ hf), MvPolynomial.isNilpotent_iff_of_fintype]
  lift f to Fin n ↪ σ using hf
  refine ⟨fun H i ↦ ?_, fun H i ↦ by simpa using H (i.embDomain f)⟩
  by_cases H : i ∈ Set.range (Finsupp.embDomain f)
  · aesop
  · rw [coeff_rename_eq_zero] <;> aesop (add simp Finsupp.embDomain_eq_mapDomain)

