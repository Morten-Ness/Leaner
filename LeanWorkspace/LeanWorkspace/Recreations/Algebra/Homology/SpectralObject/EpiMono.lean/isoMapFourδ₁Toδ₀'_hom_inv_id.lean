import Mathlib

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

variable (n₀ n₁ n₂ : ℤ) (h : IsZero ((X'.H n₂).obj (mk₁ (homOfLE hi₀₁))))

theorem isoMapFourδ₁Toδ₀'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

