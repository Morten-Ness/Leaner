import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

variable [IsAddTorsionFree R] [IsDomain R] [IsTorsionFree R M] [IsNoetherian R M] (hχ₁ : χ₁ ≠ 0)

theorem exists_genWeightSpace_smul_add_eq_bot :
    ∃ k > 0, genWeightSpace M (k • χ₁ + χ₂) = ⊥ := (Nat.eventually_pos.and <| LieModule.eventually_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁).exists

