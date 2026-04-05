import Mathlib

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

theorem intSpanEquivQuotAddOrderOf_apply_self (a : A) :
    intSpanEquivQuotAddOrderOf a ⟨a, Submodule.mem_span_singleton_self a⟩ =
    Submodule.Quotient.mk 1 := (LinearEquiv.eq_symm_apply _).mp <| Subtype.ext (one_zsmul _).symm

