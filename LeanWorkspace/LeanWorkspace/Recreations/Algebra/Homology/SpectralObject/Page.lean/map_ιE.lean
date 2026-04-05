import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  {i₀' i₁' i₂' i₃' : ι}
  (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')

set_option backward.isDefEq.respectTransparency false in
theorem map_ιE
    (γ : mk₂ f₂ f₃ ⟶ mk₂ f₂' f₃') (n₀ n₁ n₂ : ℤ)
    (hγ : γ = homMk₂ (α.app 1) (α.app 2) (α.app 3) (naturality' α 1 2)
      (naturality' α 2 3) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ ≫ X.ιE f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ =
      X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.opcyclesMap f₂ f₃ f₂' f₃' γ n₁ := by
  simp [CategoryTheory.Abelian.SpectralObject.ιE, CategoryTheory.Abelian.SpectralObject.map, X.opcyclesMap_opcyclesIso_hom f₁ f₂ f₃ f₁' f₂' f₃' α γ hγ n₀ n₁ n₂ hn₁ hn₂]

