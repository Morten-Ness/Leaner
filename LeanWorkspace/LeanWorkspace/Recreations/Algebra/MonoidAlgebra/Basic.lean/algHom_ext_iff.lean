import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem algHom_ext_iff {φ₁ φ₂ : R[M] →ₐ[R] A} : (∀ x, φ₁ (single x 1) = φ₂ (single x 1)) ↔ φ₁ = φ₂ := ⟨fun h => MonoidAlgebra.algHom_ext h, by rintro rfl _; rfl⟩

