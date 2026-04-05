import Mathlib

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

variable {C ι} (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (h : f ≫ g = fg)

theorem zero₁ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ ≫ (X.H n₁).map (twoδ₂Toδ₁ f g fg h) = 0 := by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).zero 0

