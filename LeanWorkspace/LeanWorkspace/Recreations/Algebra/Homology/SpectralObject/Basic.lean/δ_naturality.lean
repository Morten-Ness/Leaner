import Mathlib

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

variable {C ι} (X : SpectralObject C ι)

theorem δ_naturality {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g')
    (n₀ n₁ : ℤ) (hαβ : α.app 1 = β.app 0 := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).map β ≫ X.δ f' g' n₀ n₁ hn₁ = X.δ f g n₀ n₁ hn₁ ≫ (X.H n₁).map α := by
  have h := (X.δ' n₀ n₁ hn₁).naturality
    (homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
      (by simpa only [hαβ] using naturality' β 0 1) : mk₂ f g ⟶ mk₂ f' g')
  dsimp at h
  convert h <;> cat_disch

