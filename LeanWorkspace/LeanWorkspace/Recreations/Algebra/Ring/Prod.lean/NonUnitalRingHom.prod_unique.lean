import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

variable [NonUnitalNonAssocSemiring T] (f : R →ₙ+* S) (g : R →ₙ+* T)

theorem prod_unique (f : R →ₙ+* S × T) : ((NonUnitalRingHom.fst S T).comp f).prod ((NonUnitalRingHom.snd S T).comp f) = f := ext fun x => by simp only [NonUnitalRingHom.prod_apply, NonUnitalRingHom.coe_fst, NonUnitalRingHom.coe_snd, comp_apply]

