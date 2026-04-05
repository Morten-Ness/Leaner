import Mathlib

variable {F G R A B : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [FunLike G B A] [NonUnitalAlgHomClass G R B A] [StarHomClass G B A]

theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarAlgEquiv.ofBijective f hf) a = f a := rfl

