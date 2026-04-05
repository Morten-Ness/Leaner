import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ : ι} (f : i₀ ⟶ i₁) (n₀ n₁ : ℤ)

theorem opcyclesIsoH_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) :
      X.fromOpcycles f (𝟙 _) f (by simp) n₁ ≫
        (X.opcyclesIsoH f n₀ n₁ hn₁).inv = 𝟙 _ := by
  simpa using (X.opcyclesIsoH f n₀ n₁ hn₁).hom_inv_id

