import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem coe_map (f : M →* N) (x : Mˣ) : ↑(Units.map f x) = f x := rfl

