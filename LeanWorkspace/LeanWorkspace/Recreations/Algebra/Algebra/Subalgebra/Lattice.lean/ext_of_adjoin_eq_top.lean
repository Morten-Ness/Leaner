import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem ext_of_adjoin_eq_top {s : Set A} (h : Algebra.adjoin R s = ⊤) ⦃φ₁ φ₂ : A →ₐ[R] B⦄
    (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂ := ext fun _x => AlgHom.adjoin_le_equalizer φ₁ φ₂ hs <| h.symm ▸ trivial

