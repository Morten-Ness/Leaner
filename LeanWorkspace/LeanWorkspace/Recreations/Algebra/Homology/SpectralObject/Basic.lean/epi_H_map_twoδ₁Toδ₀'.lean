import Mathlib

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

variable {C ι} (X : SpectralObject C ι)

variable {ι' : Type*} [Preorder ι'] (X' : SpectralObject C ι')
  (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (i₀ i₁ i₂ : ι') (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂)
  (h₁ : IsZero ((X'.H n₀).obj (mk₁ (homOfLE h₀₁))))
  (h₂ : IsZero ((X'.H n₁).obj (mk₁ (homOfLE h₀₁))))

include h₂ hn₁ in
theorem epi_H_map_twoδ₁Toδ₀' : Epi ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂)) := X'.epi_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₂

