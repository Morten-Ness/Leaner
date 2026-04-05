import Mathlib

theorem hom_ofHom {M N : Type u} [Monoid M] [Monoid N] (f : M →* N) : (ofHom f).hom = f := rfl

