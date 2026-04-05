import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem single_neg (a : ι) (b : G) : single a (-b) = -single a b := (Finsupp.singleAddHom a : G →+ _).map_neg b

