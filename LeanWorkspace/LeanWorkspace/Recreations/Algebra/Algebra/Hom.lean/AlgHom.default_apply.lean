import Mathlib

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
  [Subsingleton T]

theorem AlgHom.default_apply (x : S) : (default : S →ₐ[R] T) x = 0 := rfl

