import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

variable {A : C} {n : ℤ} (x : A ⟶ (X.H n).obj (mk₁ fg))
  (hx : x ≫ (X.H n).map (twoδ₁Toδ₀ f g fg h) = 0)

theorem liftOpcycles_fromOpcycles :
    X.liftOpcycles f g fg h x hx ≫ X.fromOpcycles f g fg h n = x := (X.kernelSequenceOpcycles_exact f g fg h n).lift_f x hx

