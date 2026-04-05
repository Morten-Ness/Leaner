import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem coeHom_apply (x : Mˣ) : Units.coeHom M x = ↑x := rfl

