import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem mapRange_add' [FunLike F M N] [AddMonoidHomClass F M N] {f : F} (g₁ g₂ : ι →₀ M) :
    mapRange f (map_zero f) (g₁ + g₂) = mapRange f (map_zero f) g₁ + mapRange f (map_zero f) g₂ := Finsupp.mapRange_add (map_add f) g₁ g₂

