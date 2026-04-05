import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem coe_map_inv (f : M →* N) (u : Mˣ) : ↑(Units.map f u)⁻¹ = f ↑u⁻¹ := rfl

