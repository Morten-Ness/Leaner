import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

set_option backward.isDefEq.respectTransparency false in
theorem D₁_totalShift₂XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁') :
    ((shiftFunctor₂ C y).obj K).D₁ (up ℤ) n₀ n₁ ≫ (K.totalShift₂XIso y n₁ n₁' h₁).hom =
      y.negOnePow • ((K.totalShift₂XIso y n₀ n₀' h₀).hom ≫ K.D₁ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [HomologicalComplex₂.totalShift₂XIso]
    rw [ι_D₁_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, Linear.units_smul_comp,
      ι_D₁, smul_smul, ((shiftFunctor₂ C y).obj K).d₁_eq _ rfl _ _ (by dsimp; lia),
      K.d₁_eq _ rfl _ _ (by dsimp; lia)]
    dsimp
    rw [one_smul, one_smul, Category.assoc, ι_totalDesc, Linear.comp_units_smul,
      ← Int.negOnePow_add]
    congr 2
    linarith
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

