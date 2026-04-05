import Mathlib

open scoped Polynomial

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

theorem of_aeval_smul (f : R[X]) (m : M) : Module.AEval.of R M a (Polynomial.aeval a f • m) = f • Module.AEval.of R M a m := rfl

