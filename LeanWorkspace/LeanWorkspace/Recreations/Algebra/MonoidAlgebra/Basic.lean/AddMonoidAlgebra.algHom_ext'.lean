import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem algHom_ext' ⦃φ₁ φ₂ : R[M] →ₐ[R] A⦄
    (h : (φ₁ : R[M] →* A).comp (of R M) = (φ₂ : R[M] →* A).comp (of R M)) :
    φ₁ = φ₂ := MonoidAlgebra.algHom_ext <| DFunLike.congr_fun h

