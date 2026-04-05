import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

variable [NonAssocSemiring T] (f : R →+* S) (g : R →+* T)

theorem prod_apply (x) : f.prod g x = (f x, g x) := rfl

