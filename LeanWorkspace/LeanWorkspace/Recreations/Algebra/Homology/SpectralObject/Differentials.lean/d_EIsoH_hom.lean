import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂)
  (n₀ n₁ n₂ n₃ : ℤ)

theorem d_EIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      (X.EIsoH f₁ n₁ n₂ n₃ hn₂ hn₃).hom =
    (X.EIsoH f₂ n₀ n₁ n₂ hn₁ hn₂).hom ≫ X.δ f₁ f₂ n₁ n₂ hn₂ := by
  rw [← cancel_epi (X.πE (𝟙 i₁) f₂ (𝟙 i₂) n₀ n₁ n₂ hn₁ hn₂),
    ← cancel_epi (X.toCycles (𝟙 i₁) f₂ f₂ (by simp) n₁),
    X.toCycles_πE_d_assoc (𝟙 i₀) f₁ (𝟙 i₁) f₂ (𝟙 i₂) f₁ (by simp) _ _ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃,
    CategoryTheory.Abelian.SpectralObject.πE_EIsoH_hom .., πE_EIsoH_hom_assoc .., cyclesIsoH_inv_hom_id ..,
    comp_id, cyclesIsoH_inv_hom_id_assoc ..]

