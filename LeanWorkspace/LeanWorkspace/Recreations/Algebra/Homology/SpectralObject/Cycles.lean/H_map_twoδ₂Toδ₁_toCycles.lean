import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

theorem H_map_twoδ₂Toδ₁_toCycles (n : ℤ) :
    (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ X.toCycles f g fg h n = 0 := by
  simp [← cancel_mono (X.iCycles f g n)]

