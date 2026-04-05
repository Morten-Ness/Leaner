import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

private theorem isCompl_genWeightSpace_zero_posFittingComp_aux
    (h : ∀ N < (⊤ : LieSubmodule R L M), IsCompl (LieModule.genWeightSpace N 0) (LieModule.posFittingComp R L N)) :
    IsCompl (LieModule.genWeightSpace M 0) (LieModule.posFittingComp R L M) := by
  set M₀ := LieModule.genWeightSpace M (0 : L → R)
  set M₁ := LieModule.posFittingComp R L M
  rcases forall_or_exists_not (fun (x : L) ↦ LieModule.genWeightSpaceOf M (0 : R) x = ⊤)
    with h | ⟨x, hx : LieModule.genWeightSpaceOf M (0 : R) x ≠ ⊤⟩
  · suffices IsNilpotent L M by simp [M₀, M₁, isCompl_top_bot]
    replace h : M₀ = ⊤ := by simpa [M₀, LieModule.genWeightSpace]
    rw [← LieModule.isNilpotent_of_top_iff' (R := R), ← h]
    infer_instance
  · set M₀ₓ := LieModule.genWeightSpaceOf M (0 : R) x
    set M₁ₓ := LieModule.posFittingCompOf R M x
    set M₀ₓ₀ := LieModule.genWeightSpace M₀ₓ (0 : L → R)
    set M₀ₓ₁ := LieModule.posFittingComp R L M₀ₓ
    have h₁ : IsCompl M₀ₓ M₁ₓ := LieModule.isCompl_genWeightSpaceOf_zero_posFittingCompOf R L M x
    have h₂ : IsCompl M₀ₓ₀ M₀ₓ₁ := h M₀ₓ hx.lt_top
    have h₃ : M₀ₓ₀.map M₀ₓ.incl = M₀ := by
      rw [LieModule.map_genWeightSpace_eq_of_injective M₀ₓ.injective_incl, inf_eq_left,
        LieSubmodule.range_incl]
      exact iInf_le _ x
    have h₄ : M₀ₓ₁.map M₀ₓ.incl ⊔ M₁ₓ = M₁ := by
      apply le_antisymm <| sup_le_iff.mpr
        ⟨LieModule.map_posFittingComp_le _, LieModule.posFittingCompOf_le_posFittingComp R L M x⟩
      rw [← LieModule.posFittingComp_map_incl_sup_of_codisjoint h₁.codisjoint]
      exact sup_le_sup_left LieSubmodule.map_incl_le _
    rw [← h₃, ← h₄]
    apply Disjoint.isCompl_sup_right_of_isCompl_sup_left
    · rw [disjoint_iff, ← LieSubmodule.map_inf M₀ₓ.injective_incl, h₂.inf_eq_bot,
        LieSubmodule.map_bot]
    · rwa [← LieSubmodule.map_sup, h₂.sup_eq_top, LieModuleHom.map_top, LieSubmodule.range_incl]


theorem iSup_genWeightSpaceOf_eq_top [IsTriangularizable R L M] (x : L) :
    ⨆ (φ : R), LieModule.genWeightSpaceOf M φ x = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule,
    LieSubmodule.top_toSubmodule]
  dsimp [LieModule.genWeightSpaceOf]
  exact IsTriangularizable.maxGenEigenspace_eq_top x

