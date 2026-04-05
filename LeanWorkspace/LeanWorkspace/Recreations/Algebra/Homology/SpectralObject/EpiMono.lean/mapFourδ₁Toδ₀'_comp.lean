import Mathlib

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

theorem mapFourδ₁Toδ₀'_comp (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₃ i₄ i₅ hi₀₁ (hi₁₂.trans hi₂₃) hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₁Toδ₀' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₁Toδ₀' i₀ i₂ i₃ i₄ i₅ (hi₀₁.trans hi₁₂) hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ :=
  (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

