import Mathlib

variable {R A B C : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem prod_fst_snd : AlgHom.prod (AlgHom.fst R A B) (AlgHom.snd R A B) = AlgHom.id R _ := rfl

