import Mathlib

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

variable {φ' : S →* R} {ψ : S →* T} {χ : R →* T}

variable {B₁ : Type*} [NonUnitalNonAssocSemiring B₁] [DistribMulAction R B₁]

theorem coe_inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : (NonUnitalAlgHom.inverse f g h₁ h₂ : B₁ → A) = g := rfl

