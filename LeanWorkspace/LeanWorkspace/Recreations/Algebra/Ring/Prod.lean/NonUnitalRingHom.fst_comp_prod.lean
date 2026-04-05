import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

variable [NonUnitalNonAssocSemiring T] (f : R →ₙ+* S) (g : R →ₙ+* T)

theorem fst_comp_prod : (NonUnitalRingHom.fst S T).comp (f.prod g) = f := ext fun _ => rfl

