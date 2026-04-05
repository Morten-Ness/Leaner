import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ : ι} (f : i₀ ⟶ i₁) (n₀ n₁ : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem opcyclesIsoH_hom (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.opcyclesIsoH f n₀ n₁ hn₁).hom = X.fromOpcycles f (𝟙 _) f (by simp) n₁ := by
  rw [← cancel_epi (X.pOpcycles f (𝟙 _) n₁), p_fromOpcycles]
  dsimp [CategoryTheory.Abelian.SpectralObject.opcyclesIsoH]
  simp only [p_opcyclesIso_inv_assoc, homologyDataIdId_right_p, ← Functor.map_id,
    ShortComplex.RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  congr 1
  cat_disch

