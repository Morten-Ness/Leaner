import Mathlib

open scoped Polynomial

variable {R K M A : Type*} {a : A}

theorem isTorsion_of_finiteDimensional [Field K] [Ring A] [Algebra K A]
    [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M] [FiniteDimensional K A] :
    IsTorsion K[X] (Module.AEval K M a) := Module.AEval.isTorsion_of_aeval_eq_zero (minpoly.aeval K a) (minpoly.ne_zero_of_finite K a)

