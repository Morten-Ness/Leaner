import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M] (hχ₁ : χ₁ ≠ 0)

theorem exists₂_genWeightSpace_smul_add_eq_bot :
    ∃ᵉ (p < (0 : ℤ)) (q > (0 : ℤ)),
      genWeightSpace M (p • χ₁ + χ₂) = ⊥ ∧
      genWeightSpace M (q • χ₁ + χ₂) = ⊥ := by
  obtain ⟨q, hq₀, hq⟩ := LieModule.exists_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := LieModule.exists_genWeightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : ℤ), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast_zsmul]
    exact hq

