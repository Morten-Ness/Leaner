import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem iff_monoidHom_rangeRestrict :
    Function.MulExact f g ↔ Function.MulExact f.range.subtype g.rangeRestrict := Function.MulExact.iff_rangeFactorization (one_mem g.range)

