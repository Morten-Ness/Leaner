import Mathlib

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

variable {C ι} (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (h : f ≫ g = fg)

theorem composableArrows₅_exact (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.composableArrows₅ f g fg h n₀ n₁ hn₁).Exact :=
  exact_of_δ₀ (X.exact₂ _ _ _ h n₀).exact_toComposableArrows
    (exact_of_δ₀ (X.exact₃ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
      (exact_of_δ₀ (X.exact₁ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
        ((X.exact₂ _ _ _ h n₁).exact_toComposableArrows)))

