import Mathlib

variable (R A B C : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C]

theorem prod_fst_snd : StarAlgHom.prod (StarAlgHom.fst R A B) (StarAlgHom.snd R A B) = 1 := DFunLike.coe_injective Pi.prod_fst_snd

