import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]

variable (f : R →ₙ+* R') (g : S →ₙ+* S')

theorem prod_comp_prodMap (f : T →ₙ+* R) (g : T →ₙ+* S) (f' : R →ₙ+* R') (g' : S →ₙ+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) := rfl

