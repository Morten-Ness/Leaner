import Mathlib

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

theorem coe_list_prod (l : List S) : (l.prod : M) = (l.map (↑)).prod := map_list_prod (SubmonoidClass.subtype S : _ →* M) l

