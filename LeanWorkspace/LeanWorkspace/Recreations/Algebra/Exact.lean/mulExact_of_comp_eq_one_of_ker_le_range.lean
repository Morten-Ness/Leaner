import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem mulExact_of_comp_eq_one_of_ker_le_range
    (h1 : g.comp f = 1) (h2 : ker g ≤ range f) : Function.MulExact f g := Function.MulExact.of_comp_of_mem_range (congrArg DFunLike.coe h1) h2

