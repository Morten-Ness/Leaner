import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) {i j : ι} (f : i ⟶ j)

set_option backward.isDefEq.respectTransparency false in
theorem cyclesIsoH_hom_EIsoH_inv :
    (X.cyclesIsoH f n₁ n₂ hn₂).hom ≫ (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).inv =
      X.πE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ := by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂).left
  have : h.cyclesIso.inv =
      X.toCycles (𝟙 i) f f (by simp) n₁ ≫
        (X.cyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).inv := by
    rw [← cancel_mono (X.cyclesIso ..).hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← cancel_mono (X.iCycles ..), Category.assoc, CategoryTheory.Abelian.SpectralObject.cyclesIso_hom_i ..,
      h.cyclesIso_inv_comp_iCycles, toCycles_i]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₀ = n₁ - 1 := by lia
  rw [← cancel_epi (X.cyclesIsoH f n₁ n₂ hn₂).inv,
    CategoryTheory.Abelian.SpectralObject.cyclesIsoH_inv .., cyclesIsoH_inv_hom_id_assoc ..]
  dsimp [CategoryTheory.Abelian.SpectralObject.EIsoH]
  rw [← cancel_epi h.π, h.π_comp_homologyIso_inv]
  simp [CategoryTheory.Abelian.SpectralObject.πE, h, this]

