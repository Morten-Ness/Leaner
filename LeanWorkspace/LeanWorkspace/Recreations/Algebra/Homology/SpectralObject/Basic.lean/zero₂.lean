import Mathlib

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

variable {C ι} (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (h : f ≫ g = fg)

theorem zero₂ (fg : i ⟶ k) (h : f ≫ g = fg) (n₀ : ℤ) :
    (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ (X.H n₀).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).zero 0

