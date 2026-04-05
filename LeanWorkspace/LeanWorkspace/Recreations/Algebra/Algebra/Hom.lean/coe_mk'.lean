import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(AlgHom.mk' f h) = f := rfl

