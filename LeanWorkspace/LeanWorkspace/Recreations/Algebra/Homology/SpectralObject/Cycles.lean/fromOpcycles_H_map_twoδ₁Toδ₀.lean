import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

theorem fromOpcycles_H_map_twoδ₁Toδ₀ (n : ℤ) :
    X.fromOpcycles f g fg h n ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  simp [← cancel_epi (X.pOpcycles f g n)]

