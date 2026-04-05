import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem algebraMap_injective : Function.Injective (algebraMap R A) := (faithfulSMul_iff_algebraMap_injective R A).mp inferInstance

