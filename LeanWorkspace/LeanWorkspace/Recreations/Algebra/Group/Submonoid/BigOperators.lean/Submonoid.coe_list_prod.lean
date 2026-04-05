import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem coe_list_prod (l : List s) : (l.prod : M) = (l.map (↑)).prod := map_list_prod s.subtype l

