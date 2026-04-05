import Mathlib

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

variable (φ : A →ₐ[R] B)

theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₐ[R] B) = f := rfl

