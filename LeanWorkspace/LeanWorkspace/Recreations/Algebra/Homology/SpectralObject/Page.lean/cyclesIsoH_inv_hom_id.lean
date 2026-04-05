import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ : ι} (f : i₀ ⟶ i₁) (n₀ n₁ : ℤ)

theorem cyclesIsoH_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.toCycles (𝟙 _) f f (by simp) n₀ ≫
      (X.cyclesIsoH f n₀ n₁ hn₁).hom = 𝟙 _ := by
  simpa using (X.cyclesIsoH f n₀ n₁ hn₁).inv_hom_id

