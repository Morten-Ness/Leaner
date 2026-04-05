import Mathlib

variable {R A B C : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem prod_comp {C' : Type*} [Semiring C'] [Algebra R C']
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) (g' : B →ₐ[R] C') :
    (g.prod g').comp f = (g.comp f).prod (g'.comp f) := rfl

