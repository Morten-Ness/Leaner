import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

theorem IsTorsionBy.mk_smul [(Ideal.span {r}).IsTwoSided] (hM : IsTorsionBy R M r) (b : R) (x : M) :
    haveI := hM.hasSMul
    Ideal.Quotient.mk (Ideal.span {r}) b • x = b • x :=
  rfl

-- adding `@[implicit_reducible]` causes downstream breakage

