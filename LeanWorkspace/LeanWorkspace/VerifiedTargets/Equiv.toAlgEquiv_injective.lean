import Mathlib

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

theorem toAlgEquiv_injective [FaithfulSMul G A] :
    Function.Injective (MulSemiringAction.toAlgEquiv R A : G → A ≃ₐ[R] A) := fun _ _ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r

