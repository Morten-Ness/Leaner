import Mathlib

variable {G : Type*} {H : Type*} {M : Type*} {N : Type*} {P : Type*}

variable [Mul M] [Mul N]

theorem SemiconjBy.prod {x y z : M × N}
    (hm : SemiconjBy x.1 y.1 z.1) (hn : SemiconjBy x.2 y.2 z.2) : SemiconjBy x y z := Prod.ext hm hn

