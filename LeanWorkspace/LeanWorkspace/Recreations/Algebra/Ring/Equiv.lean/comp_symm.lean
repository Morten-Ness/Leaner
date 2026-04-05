import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocSemiring R] [NonAssocSemiring S] (f : R ≃+* S) (x : R)

theorem comp_symm (e : R ≃+* S) : (e : R →+* S).comp (e.symm : S →+* R) = RingHom.id S := RingHom.ext RingEquiv.apply_symm_apply e

