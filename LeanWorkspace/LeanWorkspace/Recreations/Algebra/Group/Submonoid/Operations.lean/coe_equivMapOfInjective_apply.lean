import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem coe_equivMapOfInjective_apply (f : M →* N) (hf : Function.Injective f) (x : S) :
    (Submonoid.equivMapOfInjective S f hf x : N) = f x := rfl

