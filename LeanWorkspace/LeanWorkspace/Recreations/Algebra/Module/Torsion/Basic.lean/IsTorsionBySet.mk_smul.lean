import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

theorem IsTorsionBySet.mk_smul [I.IsTwoSided] (hM : IsTorsionBySet R M I) (b : R) (x : M) :
    haveI := hM.hasSMul
    Ideal.Quotient.mk I b • x = b • x :=
  rfl

