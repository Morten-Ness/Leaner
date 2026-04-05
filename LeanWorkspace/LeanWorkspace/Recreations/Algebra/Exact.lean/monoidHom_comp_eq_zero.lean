import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem monoidHom_comp_eq_zero (h : Function.MulExact f g) : g.comp f = 1 := DFunLike.coe_injective Function.MulExact.comp_eq_one h

