import Mathlib

variable {F G A B : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [FunLike F A B] [NonUnitalRingHomClass F A B] [NonUnitalStarRingHomClass F A B]

variable [FunLike G B A]

theorem ofBijective_apply {f : F} (hf : Function.Bijective f) (a : A) :
    (StarRingEquiv.ofBijective f hf) a = f a := rfl

