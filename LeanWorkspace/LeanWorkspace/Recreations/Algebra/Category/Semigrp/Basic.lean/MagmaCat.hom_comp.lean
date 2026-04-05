import Mathlib

theorem hom_comp {M N T : MagmaCat} (f : M ⟶ N) (g : N ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

