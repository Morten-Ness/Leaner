import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s t : Subsemiring R}

theorem subsemiringMap_symm_apply_coe (e : R ≃+* S) (s : Subsemiring R) (x : s.map e.toRingHom) :
    ((RingEquiv.subsemiringMap e s).symm x : R) = e.symm x := rfl

