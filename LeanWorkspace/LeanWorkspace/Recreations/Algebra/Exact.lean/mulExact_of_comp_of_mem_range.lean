import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem mulExact_of_comp_of_mem_range
    (h1 : g.comp f = 1) (h2 : ∀ x, g x = 1 → x ∈ range f) : Function.MulExact f g := MonoidHom.mulExact_of_comp_eq_one_of_ker_le_range h1 h2

