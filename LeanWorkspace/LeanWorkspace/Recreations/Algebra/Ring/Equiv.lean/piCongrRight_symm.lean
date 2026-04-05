import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

variable [FunLike F R S]

theorem piCongrRight_symm {ι : Type*} {R S : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (R i)]
    [∀ i, NonUnitalNonAssocSemiring (S i)] (e : ∀ i, R i ≃+* S i) :
    (RingEquiv.piCongrRight e).symm = RingEquiv.piCongrRight fun i => (e i).symm := rfl

