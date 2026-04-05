import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem _root_.MonoidHom.compAddChar_apply (f : M →* N) (φ : AddChar A M) : f.compAddChar φ = f ∘ φ := rfl

