import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+ B) := RingHom.coe_addMonoidHom_injective.comp AlgHom.coe_ringHom_injective

