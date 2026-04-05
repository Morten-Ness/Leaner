import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

variable {A : C} {n : ℤ} (x : (X.H n).obj (mk₁ fg) ⟶ A)
  (hx : (X.H n).map (twoδ₂Toδ₁ f g fg h) ≫ x = 0)

theorem toCycles_descCycles :
    X.toCycles f g fg h n ≫ X.descCycles f g fg h x hx = x := (X.cokernelSequenceCycles_exact f g fg h n).g_desc x hx

