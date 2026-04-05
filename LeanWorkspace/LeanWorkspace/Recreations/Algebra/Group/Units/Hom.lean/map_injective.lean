import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem map_injective {f : M →* N} (hf : Function.Injective f) :
    Function.Injective (Units.map f) := fun _ _ e => ext (hf (congr_arg val e))

