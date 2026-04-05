import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem _root_.RingHom.smulOneHom_eq_algebraMap : RingHom.smulOneHom = algebraMap R A := RingHom.ext fun r => (Algebra.algebraMap_eq_smul_one r).symm

-- TODO: set up `IsScalarTower.smulCommClass` earlier so that we can actually prove this using
-- `mul_smul_comm s x y`.

