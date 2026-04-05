import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_fun_curry (f : ι × κ → M) :
    Function.mulSupport (fun i j ↦ f (i, j)) = (Function.mulSupport f).image Prod.fst := Function.mulSupport_curry f

