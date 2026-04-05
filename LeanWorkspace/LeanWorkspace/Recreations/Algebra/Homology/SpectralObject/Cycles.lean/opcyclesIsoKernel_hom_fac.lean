import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

theorem opcyclesIsoKernel_hom_fac (n : ℤ) :
    X.pOpcycles f g n ≫ (X.opcyclesIsoKernel f g fg h n).hom ≫
      kernel.ι _ = (X.H n).map (twoδ₂Toδ₁ f g fg h) := (X.composableArrows₅_exact f g fg h (n - 1) n).cokerIsoKer_hom_fac 2

