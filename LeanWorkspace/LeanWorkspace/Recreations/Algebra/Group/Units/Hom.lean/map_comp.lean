import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem map_comp (f : M →* N) (g : N →* P) : Units.map (g.comp f) = (Units.map g).comp (Units.map f) := rfl

