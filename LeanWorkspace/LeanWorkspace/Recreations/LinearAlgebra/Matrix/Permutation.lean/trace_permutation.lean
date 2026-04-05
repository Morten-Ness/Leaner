import Mathlib

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable [Fintype n]

theorem trace_permutation [AddCommMonoidWithOne R] :
    trace (σ.permMatrix R) = (Function.fixedPoints σ).ncard := by
  delta trace
  simp [toPEquiv_apply, ← Set.ncard_coe_finset, Function.fixedPoints, Function.IsFixedPt]

