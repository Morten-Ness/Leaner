import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem ofInjective_apply (f : A →ₐ[R] B) (hf : Function.Injective f) (x : A) :
    ↑(AlgEquiv.ofInjective f hf x) = f x := rfl

