import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem coeHom_injective : Function.Injective (Units.coeHom M) := Units.val_injective

