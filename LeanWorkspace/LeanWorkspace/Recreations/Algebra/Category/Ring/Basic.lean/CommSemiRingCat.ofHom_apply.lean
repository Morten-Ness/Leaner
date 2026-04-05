import Mathlib

theorem ofHom_apply {R S : Type u} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

