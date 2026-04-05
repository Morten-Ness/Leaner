import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

theorem cokernelIsoCycles_hom_fac (n : ℤ) :
    cokernel.π _ ≫ (X.cokernelIsoCycles f g fg h n).hom ≫
      X.iCycles f g n = (X.H n).map (twoδ₁Toδ₀ f g fg h) := (X.composableArrows₅_exact f g fg h n (n + 1)).cokerIsoKer_hom_fac 0

