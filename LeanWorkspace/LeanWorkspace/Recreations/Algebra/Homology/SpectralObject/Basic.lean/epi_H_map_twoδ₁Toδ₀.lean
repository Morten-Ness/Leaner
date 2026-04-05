import Mathlib

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

variable {C ι} (X : SpectralObject C ι)

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i₀ i₁ i₂ : ι}
  (f : i₀ ⟶ i₁) (g : i₁ ⟶ i₂) (fg : i₀ ⟶ i₂) (hfg : f ≫ g = fg)
  (h₁ : IsZero ((X.H n₀).obj (mk₁ f))) (h₂ : IsZero ((X.H n₁).obj (mk₁ f)))

include h₂ hn₁ in
theorem epi_H_map_twoδ₁Toδ₀ : Epi ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg)) := (X.exact₃ f g fg hfg n₀ n₁ hn₁).epi_f (h₂.eq_of_tgt _ _)

