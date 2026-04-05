import Mathlib

theorem hom_ofHom {R S : Type u} [Group R] [Group S] (f : R →* S) : (ofHom f).hom = f := rfl

