import Mathlib

open scoped Polynomial

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

theorem compAEval_eq (d : Derivation R A M) (f : R[X]) :
    d.compAEval a f = derivative f • (AEval.of R M a (d a)) := by
  simpa using AEval.of_aeval_smul _ _ _

