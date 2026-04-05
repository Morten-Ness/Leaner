import Mathlib

variable {F α β R S S' : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R ≃+* S) (x : R)

variable [FunLike F R S]

theorem coe_prodCongr {R R' S S' : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S] [NonUnitalNonAssocSemiring S']
    (f : R ≃+* R') (g : S ≃+* S') :
    ⇑(RingEquiv.prodCongr f g) = Prod.map f g := rfl

