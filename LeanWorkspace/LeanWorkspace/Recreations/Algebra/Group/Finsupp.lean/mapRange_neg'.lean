import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem mapRange_neg' [SubtractionMonoid H] [FunLike F G H] [AddMonoidHomClass F G H]
    {f : F} (v : ι →₀ G) :
    mapRange f (map_zero f) (-v) = -mapRange f (map_zero f) v := Finsupp.mapRange_neg (map_neg f) v

