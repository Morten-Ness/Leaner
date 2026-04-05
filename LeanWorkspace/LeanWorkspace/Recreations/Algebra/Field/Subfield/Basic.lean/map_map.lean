import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (s t : Subfield K)

variable (f : K →+* L)

theorem map_map (g : L →+* M) (f : K →+* L) : (s.map f).map g = s.map (g.comp f) := SetLike.ext' <| Set.image_image _ _ _

