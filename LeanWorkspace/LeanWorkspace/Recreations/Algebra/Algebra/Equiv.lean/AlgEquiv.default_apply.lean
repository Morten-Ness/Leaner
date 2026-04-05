import Mathlib

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]

theorem AlgEquiv.default_apply [Subsingleton S] [Subsingleton T] (x : S) :
    (default : S ≃ₐ[R] T) x = 0 := rfl

