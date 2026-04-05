import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem subtype_comp_inclusion {S T : Submonoid M} (h : S ≤ T) :
    T.subtype.comp (Submonoid.inclusion h) = S.subtype := rfl

