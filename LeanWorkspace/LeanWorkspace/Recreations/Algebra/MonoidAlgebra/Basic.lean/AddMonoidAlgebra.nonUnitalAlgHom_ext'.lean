import Mathlib

variable {R S T A B C M N O : Type*}

variable (R) [Semiring R] [Add M] [NonUnitalNonAssocSemiring A]

theorem nonUnitalAlgHom_ext' [DistribMulAction R A] {φ₁ φ₂ : R[M] →ₙₐ[R] A}
    (h : φ₁.toMulHom.comp (ofMagma R M) = φ₂.toMulHom.comp (ofMagma R M)) : φ₁ = φ₂ := MonoidAlgebra.nonUnitalAlgHom_ext R <| DFunLike.congr_fun h

