import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem inclusion_injective {S T : Submonoid M} (h : S ≤ T) : Function.Injective <| Submonoid.inclusion h := Set.inclusion_injective h

