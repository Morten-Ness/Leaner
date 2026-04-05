import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem coe_inclusion {S T : Submonoid M} (h : S ≤ T) (a : S) : (Submonoid.inclusion h a : M) = a := Set.coe_inclusion h a

