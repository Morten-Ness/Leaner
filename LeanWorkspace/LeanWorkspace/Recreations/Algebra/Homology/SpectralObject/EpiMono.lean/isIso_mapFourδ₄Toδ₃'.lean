import Mathlib

variable {C ι ι' κ : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

variable (n₀ n₁ n₂ : ℤ) (h : IsZero ((X'.H n₀).obj (mk₁ (homOfLE hi₃₄))))

include h in
theorem isIso_mapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map_fourδ₄Toδ₃_of_isZero (h := h) ..

