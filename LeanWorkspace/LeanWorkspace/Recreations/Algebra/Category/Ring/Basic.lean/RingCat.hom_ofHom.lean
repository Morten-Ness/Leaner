import Mathlib

theorem hom_ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) : (ofHom f).hom = f := rfl

