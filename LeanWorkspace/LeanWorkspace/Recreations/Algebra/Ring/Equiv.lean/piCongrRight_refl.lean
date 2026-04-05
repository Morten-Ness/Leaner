import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

variable [FunLike F R S]

theorem piCongrRight_refl {ι : Type*} {R : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)] :
    (RingEquiv.piCongrRight fun i => RingEquiv.refl (R i)) = RingEquiv.refl _ := rfl

