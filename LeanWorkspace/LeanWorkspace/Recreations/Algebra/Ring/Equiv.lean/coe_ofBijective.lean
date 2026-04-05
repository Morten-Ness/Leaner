import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

variable [FunLike F R S]

theorem coe_ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    (RingEquiv.ofBijective f hf : R → S) = f := rfl

