import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x := DFunLike.congr_fun H x

