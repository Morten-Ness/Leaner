import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem mulExact_iff :
    Function.MulExact f g ↔ ker g = range f := Iff.symm SetLike.ext_iff

