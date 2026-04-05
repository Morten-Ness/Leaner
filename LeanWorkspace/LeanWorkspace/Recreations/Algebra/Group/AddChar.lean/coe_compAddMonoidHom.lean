import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem coe_compAddMonoidHom (φ : AddChar B M) (f : A →+ B) : φ.compAddMonoidHom f = φ ∘ f := rfl

