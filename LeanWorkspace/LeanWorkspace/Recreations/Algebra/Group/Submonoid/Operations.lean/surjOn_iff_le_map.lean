import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem surjOn_iff_le_map {f : M →* N} {H : Submonoid M} {K : Submonoid N} :
    Set.SurjOn f H K ↔ K ≤ H.map f := Iff.rfl

