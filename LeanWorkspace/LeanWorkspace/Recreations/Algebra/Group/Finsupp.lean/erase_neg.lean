import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem erase_neg (a : ι) (f : ι →₀ G) : erase a (-f) = -erase a f := (Finsupp.eraseAddHom a : (_ →₀ G) →+ _).map_neg f

