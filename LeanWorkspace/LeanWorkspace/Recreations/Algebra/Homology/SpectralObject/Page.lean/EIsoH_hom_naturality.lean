import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j : ι} (f : i ⟶ j) {i' j' : ι} (f' : i' ⟶ j')

theorem EIsoH_hom_naturality
    (α : mk₁ f ⟶ mk₁ f') (β : mk₃ (𝟙 _) f (𝟙 _) ⟶ mk₃ (𝟙 _) f' (𝟙 _))
    (n₀ n₁ n₂ : ℤ)
    (hβ : β = homMk₃ (α.app 0) (α.app 0) (α.app 1) (α.app 1)
      (by simp) (naturality' α 0 1) (by simp [Precomp.obj, Precomp.map]) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map (𝟙 _) f (𝟙 _) (𝟙 _) f' (𝟙 _) β n₀ n₁ n₂ hn₁ hn₂ ≫
      (X.EIsoH f' n₀ n₁ n₂ hn₁ hn₂).hom =
    (X.EIsoH f n₀ n₁ n₂ hn₁ hn₂).hom ≫ (X.H n₁).map α := by
  obtain rfl : α = homMk₁ (β.app 1) (β.app 2) (naturality' β 1 2) := by
    subst hβ
    exact hom_ext₁ rfl rfl
  exact (ShortComplex.LeftHomologyMapData.ofZeros
    (X.shortComplexMap _ _ _ _ _ _ β n₀ n₁ n₂ hn₁ hn₂) ..).homologyMap_comm

