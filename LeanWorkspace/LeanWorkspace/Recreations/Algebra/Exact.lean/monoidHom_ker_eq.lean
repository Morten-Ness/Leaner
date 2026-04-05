import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem monoidHom_ker_eq (hfg : Function.MulExact f g) :
    ker g = range f := SetLike.ext hfg

