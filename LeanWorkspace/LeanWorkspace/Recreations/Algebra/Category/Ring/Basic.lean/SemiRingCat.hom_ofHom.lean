import Mathlib

theorem hom_ofHom {R S : Type u} [Semiring R] [Semiring S] (f : R →+* S) : (ofHom f).hom = f := rfl

