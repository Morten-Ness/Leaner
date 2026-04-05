import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₆ : i₅ ⟶ i₆) (f₇ : i₆ ⟶ i₇)
  (n₀ n₁ n₂ n₃ n₄ : ℤ)

theorem d_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    X.d f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄ = 0 := by
  rw [← cancel_epi (X.πE f₅ f₆ f₇ n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_epi (X.toCycles f₅ f₆ _ rfl n₁ ), comp_zero, comp_zero,
    X.toCycles_πE_d_assoc f₃ f₄ f₅ f₆ f₇ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    X.toCycles_πE_d f₁ f₂ f₃ f₄ f₅ _ rfl _ rfl n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄,
    δ_δ_assoc .., zero_comp]

