import Mathlib

theorem hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S ⟶ T) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

