import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem adjoin_le_equalizer (φ₁ φ₂ : A →ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂) :
    Algebra.adjoin R s ≤ equalizer φ₁ φ₂ := Algebra.adjoin_le h

