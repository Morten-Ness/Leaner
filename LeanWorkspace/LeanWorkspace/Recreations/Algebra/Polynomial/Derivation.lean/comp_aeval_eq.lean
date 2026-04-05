import Mathlib

open scoped Polynomial

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

theorem comp_aeval_eq (d : Derivation R A M) (f : R[X]) :
    d (Polynomial.aeval a f) = Polynomial.aeval a (derivative f) • d a := calc
    _ = (AEval.of R M a).symm (d.compAEval a f) := rfl
    _ = _ := by simp [-compAEval_apply, Derivation.compAEval_eq]

