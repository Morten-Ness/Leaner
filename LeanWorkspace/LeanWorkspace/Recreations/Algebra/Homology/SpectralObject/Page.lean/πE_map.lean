import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i₀ i₁ i₂ i₃ : ι}
  (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  {i₀' i₁' i₂' i₃' : ι}
  (f₁' : i₀' ⟶ i₁') (f₂' : i₁' ⟶ i₂') (f₃' : i₂' ⟶ i₃')
  (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂' f₃')

set_option backward.isDefEq.respectTransparency false in
theorem πE_map (β : mk₂ f₁ f₂ ⟶ mk₂ f₁' f₂') (n₀ n₁ n₂ : ℤ)
    (hβ : β = homMk₂ (α.app 0) (α.app 1) (α.app 2) (naturality' α 0 1 (by lia) (by lia))
      (naturality' α 1 2 (by lia) (by lia)) := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.map f₁ f₂ f₃ f₁' f₂' f₃' α n₀ n₁ n₂ hn₁ hn₂ =
      X.cyclesMap f₁ f₂ f₁' f₂' β n₁ ≫ X.πE f₁' f₂' f₃' n₀ n₁ n₂ hn₁ hn₂ := by
  simp [CategoryTheory.Abelian.SpectralObject.πE, CategoryTheory.Abelian.SpectralObject.map, X.cyclesIso_inv_cyclesMap_assoc f₁ f₂ f₃ f₁' f₂' f₃' α β hβ n₀ n₁ n₂]

