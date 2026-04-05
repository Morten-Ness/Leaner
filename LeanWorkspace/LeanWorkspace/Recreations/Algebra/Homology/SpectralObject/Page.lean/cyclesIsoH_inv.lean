import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ : ι} (f : i₀ ⟶ i₁) (n₀ n₁ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem cyclesIsoH_inv (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.cyclesIsoH f n₀ n₁ hn₁).inv = X.toCycles (𝟙 _) f f (by simp) n₀ := by
  rw [← cancel_mono (X.iCycles (𝟙 _) f n₀), toCycles_i]
  dsimp [CategoryTheory.Abelian.SpectralObject.cyclesIsoH]
  simp only [Category.assoc, CategoryTheory.Abelian.SpectralObject.cyclesIso_hom_i, homologyDataIdId_left_i,
    ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles, ← Functor.map_id]
  congr 1
  cat_disch

