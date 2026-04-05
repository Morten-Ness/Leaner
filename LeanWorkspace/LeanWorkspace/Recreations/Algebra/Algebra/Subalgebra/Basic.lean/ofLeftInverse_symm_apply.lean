import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem ofLeftInverse_symm_apply {g : B → A} {f : A →ₐ[R] B} (h : Function.LeftInverse g f)
    (x : f.range) : (AlgEquiv.ofLeftInverse h).symm x = g x := rfl

