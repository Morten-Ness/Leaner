import Mathlib

theorem ofHom_hom {R S : CommSemiRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

