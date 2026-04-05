import Mathlib

variable {R R' S S' T : Type*}

variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]

variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]

variable (f : R →+* R') (g : S →+* S')

theorem prod_comp_prodMap (f : T →+* R) (g : T →+* S) (f' : R →+* R') (g' : S →+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) := rfl

