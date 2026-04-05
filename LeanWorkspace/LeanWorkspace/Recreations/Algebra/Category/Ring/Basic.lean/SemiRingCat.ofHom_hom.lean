import Mathlib

theorem ofHom_hom {R S : SemiRingCat} (f : R ⟶ S) :
    ofHom (Hom.hom f) = f := rfl

