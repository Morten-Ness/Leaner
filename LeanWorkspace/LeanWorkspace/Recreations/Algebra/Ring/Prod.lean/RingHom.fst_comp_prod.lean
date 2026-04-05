import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

variable [NonAssocSemiring T] (f : R →+* S) (g : R →+* T)

theorem fst_comp_prod : (RingHom.fst S T).comp (f.prod g) = f := ext fun _ => rfl

