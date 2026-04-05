import Mathlib

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

variable {C ι} (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (h : f ≫ g = fg)

theorem exact₂ (n₀ : ℤ) :
    (X.sc₂ f g fg h n₀).Exact := by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).exact 0

