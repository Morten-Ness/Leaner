import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem coe_equivMapOfInjective_apply (f : M →ₙ* N) (hf : Function.Injective f) (x : S) :
    (Subsemigroup.equivMapOfInjective S f hf x : N) = f x := rfl

