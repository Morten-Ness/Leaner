import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M] (hχ₁ : χ₁ ≠ 0)

theorem eventually_genWeightSpace_smul_add_eq_bot :
    ∀ᶠ (k : ℕ) in Filter.atTop, genWeightSpace M (k • χ₁ + χ₂) = ⊥ := by
  let f : ℕ → L → R := fun k ↦ k • χ₁ + χ₂
  suffices Function.Injective f by
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite, ← finite_image_iff this.injOn]
    apply (finite_genWeightSpace_ne_bot R L M).subset
    simp [f]
  intro k l hkl
  replace hkl : (k : ℤ) • χ₁ = (l : ℤ) • χ₁ := by
    simpa only [f, add_left_inj, natCast_zsmul] using hkl
  exact Nat.cast_inj.mp <| smul_left_injective ℤ hχ₁ hkl

