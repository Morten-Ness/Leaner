import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem mapRange_sub' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v₁ v₂ : ι →₀ G) :
    mapRange f (map_zero f) (v₁ - v₂) = mapRange f (map_zero f) v₁ - mapRange f (map_zero f) v₂ := Finsupp.mapRange_sub (map_sub f) v₁ v₂

