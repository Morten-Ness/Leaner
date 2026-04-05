import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)
  (n₀ n₁ n₂ n₃ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem πE_EIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE (𝟙 i₀) f₁ (𝟙 i₁) n₀ n₁ n₂ hn₁ hn₂ ≫ (X.EIsoH f₁ n₀ n₁ n₂ hn₁ hn₂).hom =
      (X.cyclesIsoH f₁ n₁ n₂ hn₂).hom := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  simp [πE, cyclesIsoH, EIsoH]

