import Mathlib

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

variable {C ι} (X : SpectralObject C ι)

theorem isZero_H_map_mk₁_of_isIso (n : ℤ) {i₀ i₁ : ι} (f : i₀ ⟶ i₁) [IsIso f] :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let φ := twoδ₂Toδ₁ f (inv f) (𝟙 i₀) (by simp) ≫ twoδ₁Toδ₀ f (inv f) (𝟙 i₀)
  have : IsIso φ := by
    rw [isIso_iff₁]
    constructor <;> dsimp [φ] <;> infer_instance
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_mono ((X.H n).map φ), Category.id_comp, zero_comp,
    ← X.zero₂ f (inv f) (𝟙 _) (by simp), ← Functor.map_comp]

