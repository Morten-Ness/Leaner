import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem coe_ringHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+* B) := by
  intro f g h
  ext x
  exact DFunLike.congr_fun h x
