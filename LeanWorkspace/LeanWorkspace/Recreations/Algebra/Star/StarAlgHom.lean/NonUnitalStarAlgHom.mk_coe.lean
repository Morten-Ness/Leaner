import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

theorem mk_coe (f : A →⋆ₙₐ[R] B) (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A →⋆ₙₐ[R] B) = f := by
  ext
  rfl

