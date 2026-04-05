import Mathlib

variable {R : Type u} {S : Type u₁}

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)

variable (A : Type v) (B : Type w) (C : Type w₁)

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

theorem coe_mulHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₙ* B) = ⟨f, h₄⟩ := by
  rfl

