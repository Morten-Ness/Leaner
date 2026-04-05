import Mathlib

open scoped Algebra

variable (R S A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]

theorem IsDomain.of_faithfulSMul [IsDomain A] : IsDomain R := (FaithfulSMul.algebraMap_injective R A).isDomain

