import Mathlib

variable {R S T A B C M N O : Type*}

variable (R) [Semiring R] [Mul M] [NonUnitalNonAssocSemiring A]

theorem nonUnitalAlgHom_ext [DistribMulAction R A] {φ₁ φ₂ : R[M] →ₙₐ[R] A}
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ := NonUnitalAlgHom.to_distribMulActionHom_injective <|
    Finsupp.distribMulActionHom_ext' fun a => DistribMulActionHom.ext_ring (h a)

