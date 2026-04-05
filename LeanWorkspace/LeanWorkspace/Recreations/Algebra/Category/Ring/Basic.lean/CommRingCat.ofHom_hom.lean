import Mathlib

theorem ofHom_hom {R S : CommRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

