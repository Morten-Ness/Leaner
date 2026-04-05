import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]

variable (f : R →ₙ+* R') (g : S →ₙ+* S')

theorem prodMap_def : NonUnitalRingHom.prodMap f g = (f.comp (NonUnitalRingHom.fst R S)).prod (g.comp (NonUnitalRingHom.snd R S)) := rfl

