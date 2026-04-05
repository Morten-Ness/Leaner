import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

set_option backward.isDefEq.respectTransparency false in
theorem D₂_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₂ (up ℤ) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₂ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [HomologicalComplex₂.totalShift₁XIso]
    rw [ι_D₂_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, ι_D₂,
      ((shiftFunctor₁ C x).obj K).d₂_eq _ _ rfl _ (by dsimp; lia),
      K.d₂_eq _ _ rfl _ (by dsimp; lia), smul_smul,
      Linear.units_smul_comp, Category.assoc, ι_totalDesc]
    dsimp
    congr 1
    rw [add_comm p, Int.negOnePow_add, ← mul_assoc, Int.units_mul_self, one_mul]
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    grind [up_Rel]

