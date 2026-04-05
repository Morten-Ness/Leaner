import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring k]

theorem lhom_ext' {N : Type*} [Semiring R] [AddCommMonoid N] [Module R N] [Module R k]
    ⦃f g : k[G] →ₗ[R] N⦄
    (H : ∀ (x : G), LinearMap.comp f (lsingle x) = LinearMap.comp g (lsingle x)) :
    f = g := Finsupp.lhom_ext' H

