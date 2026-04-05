import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem algebraMap_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) := RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

