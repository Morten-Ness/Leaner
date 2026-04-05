import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

variable [NonAssocSemiring T] (f : R →+* S) (g : R →+* T)

theorem prod_unique (f : R →+* S × T) : ((RingHom.fst S T).comp f).prod ((RingHom.snd S T).comp f) = f := ext fun x => by simp only [RingHom.prod_apply, RingHom.coe_fst, RingHom.coe_snd, comp_apply]

