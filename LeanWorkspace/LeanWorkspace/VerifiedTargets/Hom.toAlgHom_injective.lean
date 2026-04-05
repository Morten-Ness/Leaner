import Mathlib

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun _m₁ _m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r

