import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ : ι} (f : i₀ ⟶ i₁) (n₀ n₁ : ℤ)

theorem cyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cyclesIsoH f n₀ n₁ hn₁).hom ≫
      X.toCycles (𝟙 _) f f (by simp) n₀ = 𝟙 _ := by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).hom_inv_id

