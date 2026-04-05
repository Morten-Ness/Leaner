import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem map_inf (s t : Subfield K) (f : K →+* L) : (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter f.injective)

