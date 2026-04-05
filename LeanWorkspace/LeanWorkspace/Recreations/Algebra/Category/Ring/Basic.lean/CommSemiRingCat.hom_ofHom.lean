import Mathlib

theorem hom_ofHom {R S : Type u} [CommSemiring R] [CommSemiring S] (f : R →+* S) :
    (ofHom f).hom = f := rfl

