import Mathlib

variable {R A B C D : Type*} [Monoid R]

variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Star A]

variable [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]

variable [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

variable [NonUnitalNonAssocSemiring D] [DistribMulAction R D] [Star D]

theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅) :
    ((⟨⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩, h₅⟩ : A →⋆ₙₐ[R] B) : A → B) = f := rfl

-- this is probably the more useful lemma for Lean 4 and should likely replace `coe_mk` above

