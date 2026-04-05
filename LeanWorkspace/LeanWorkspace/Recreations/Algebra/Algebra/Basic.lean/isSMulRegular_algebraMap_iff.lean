import Mathlib

open scoped Algebra

variable {R : Type*} [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

theorem isSMulRegular_algebraMap_iff {r : R} :
    IsSMulRegular M (algebraMap R A r) ↔ IsSMulRegular M r := (Equiv.refl M).isSMulRegular_congr (algebraMap_smul A r)

