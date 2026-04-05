import Mathlib

variable {R S T : Type*} [CommSemiring R] [Semiring S]
  [Semiring T] [Algebra R S] [Algebra R T]

theorem AlgHom.down_ulift_apply (f : S →ₐ[R] T) (x : ULift S) :
    (f.ulift x).down = f x.down := rfl

