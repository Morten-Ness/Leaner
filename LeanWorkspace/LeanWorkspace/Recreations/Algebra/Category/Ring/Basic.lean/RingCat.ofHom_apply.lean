import Mathlib

theorem ofHom_apply {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

