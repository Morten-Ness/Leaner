import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

variable [NonUnitalNonAssocSemiring T] (f : R →ₙ+* S) (g : R →ₙ+* T)

theorem snd_comp_prod : (NonUnitalRingHom.snd S T).comp (f.prod g) = g := ext fun _ => rfl

