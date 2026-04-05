import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem coe_toAddMonoidHomEquiv (ψ : AddChar A M) :
    ⇑(AddChar.toAddMonoidHomEquiv ψ) = Additive.ofMul ∘ ψ := rfl

