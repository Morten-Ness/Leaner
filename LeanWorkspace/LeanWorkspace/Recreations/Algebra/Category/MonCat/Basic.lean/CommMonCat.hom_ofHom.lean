import Mathlib

theorem hom_ofHom {M N : Type u} [CommMonoid M] [CommMonoid N] (f : M →* N) : (ofHom f).hom = f := rfl

