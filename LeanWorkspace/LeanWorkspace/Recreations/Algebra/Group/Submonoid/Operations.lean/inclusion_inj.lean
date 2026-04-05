import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem inclusion_inj {S T : Submonoid M} (h : S ≤ T) {x y : S} :
    Submonoid.inclusion h x = Submonoid.inclusion h y ↔ x = y := (Submonoid.inclusion_injective h).eq_iff

