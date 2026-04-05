import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b := (FaithfulSMul.algebraMap_injective _ _).eq_iff

