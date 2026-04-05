import Mathlib

variable {F R A B C D : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A] [Semiring B]
  [Algebra R B] [Star B] [Semiring C] [Algebra R C] [Star C] [Semiring D] [Algebra R D] [Star D]

theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄ h₅ h₆) :
    ((⟨⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩, h₆⟩ : A →⋆ₐ[R] B) : A → B) = f := rfl

-- this is probably the more useful lemma for Lean 4 and should likely replace `NonUnitalStarAlgHom.coe_mk` above

