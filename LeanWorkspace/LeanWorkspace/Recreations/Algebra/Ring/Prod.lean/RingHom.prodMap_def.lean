import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]

variable (f : R →+* R') (g : S →+* S')

theorem prodMap_def : RingHom.prodMap f g = (f.comp (RingHom.fst R S)).prod (g.comp (RingHom.snd R S)) := rfl

