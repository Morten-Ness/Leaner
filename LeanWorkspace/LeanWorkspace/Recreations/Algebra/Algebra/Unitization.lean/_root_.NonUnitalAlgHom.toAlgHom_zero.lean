import Mathlib

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

theorem _root_.NonUnitalAlgHom.toAlgHom_zero :
    ⇑(0 : A →ₙₐ[R] R).toAlgHom = (fun x ↦ x.fst) := by
  ext
  simp

