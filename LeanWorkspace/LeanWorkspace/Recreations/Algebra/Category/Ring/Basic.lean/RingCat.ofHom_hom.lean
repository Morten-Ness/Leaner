import Mathlib

theorem ofHom_hom {R S : RingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

