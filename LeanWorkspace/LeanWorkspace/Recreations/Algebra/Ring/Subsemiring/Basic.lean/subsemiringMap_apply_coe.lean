import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s t : Subsemiring R}

theorem subsemiringMap_apply_coe (e : R ≃+* S) (s : Subsemiring R) (x : s) :
    ((RingEquiv.subsemiringMap e s) x : S) = e x := rfl

