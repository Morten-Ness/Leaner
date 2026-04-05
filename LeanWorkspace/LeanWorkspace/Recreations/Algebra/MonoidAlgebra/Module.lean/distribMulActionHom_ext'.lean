import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring k]

theorem distribMulActionHom_ext' {N : Type*} [Monoid R] [AddMonoid N] [DistribMulAction R N]
    [DistribMulAction R k] {f g : k[G] →+[R] N}
    (h : ∀ a, f.comp (MonoidAlgebra.singleDistribMulActionHom a) = g.comp (MonoidAlgebra.singleDistribMulActionHom a)) :
    f = g := Finsupp.distribMulActionHom_ext' h

