import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

variable [FunLike F R S]

theorem ofBijective_apply [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
    (x : R) : RingEquiv.ofBijective f hf x = f x := rfl

