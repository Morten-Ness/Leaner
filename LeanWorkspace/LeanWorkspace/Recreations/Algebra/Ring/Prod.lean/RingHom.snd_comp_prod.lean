import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

variable [NonAssocSemiring T] (f : R →+* S) (g : R →+* T)

theorem snd_comp_prod : (RingHom.snd S T).comp (f.prod g) = g := ext fun _ => rfl

