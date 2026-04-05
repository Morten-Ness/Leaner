import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

theorem ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := Prod.ext h1 h2

