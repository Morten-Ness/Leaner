import Mathlib

theorem ofHom_apply {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) (r : R) : ofHom f r = f r := rfl

