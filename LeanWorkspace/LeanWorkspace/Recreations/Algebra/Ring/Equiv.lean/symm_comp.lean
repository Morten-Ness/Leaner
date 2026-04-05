import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

theorem symm_comp (e : R ≃+* S) : (e.symm : S →+* R).comp (e : R →+* S) = RingHom.id R := RingHom.ext RingEquiv.symm_apply_apply e

