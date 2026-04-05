import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) {i j : ι} (f : i ⟶ j)

set_option backward.isDefEq.respectTransparency false in
theorem EIsoH_hom_opcyclesIsoH_inv :
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.opcyclesIsoH f n₀ n₁ hn₁).inv =
      X.ιE (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂ := by
  let h := (X.homologyDataIdId f n₀ n₁ n₂ hn₁ hn₂)
  have : h.right.opcyclesIso.hom =
      (X.opcyclesIso (𝟙 i) f (𝟙 j) n₀ n₁ n₂ hn₁ hn₂).hom ≫
        X.fromOpcycles f (𝟙 j) f (by simp) n₁ := by
    rw [← cancel_epi (X.opcyclesIso ..).inv, Iso.inv_hom_id_assoc,
      ← cancel_epi (X.pOpcycles ..), p_opcyclesIso_inv_assoc ..,
      h.right.pOpcycles_comp_opcyclesIso_hom, p_fromOpcycles]
    dsimp [h]
    rw [← Functor.map_id]
    congr 1
    cat_disch
  obtain rfl : n₂ = n₁ + 1 := by lia
  rw [← cancel_mono (X.opcyclesIsoH f n₀ n₁ hn₁).hom, Category.assoc,
    CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_hom .., CategoryTheory.Abelian.SpectralObject.opcyclesIsoH_inv_hom_id ..]
  dsimp [CategoryTheory.Abelian.SpectralObject.EIsoH, CategoryTheory.Abelian.SpectralObject.ιE]
  rw [Category.assoc, ← this,
    h.left_homologyIso_eq_right_homologyIso_trans_iso_symm,
    ← ShortComplex.RightHomologyData.homologyIso_hom_comp_ι]
  simp [h]

