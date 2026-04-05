import Mathlib

variable {R I : Type*} [Semiring R] [DecidableEq I] (V : I → Ideal R) [Decomposition V]

theorem decompose_eq_mul_idempotent (x : R) (i : I) : decompose V x i = x * DirectSum.idempotent V i := by
  rw [← smul_eq_mul (a := x), DirectSum.idempotent, ← Submodule.coe_smul, ← smul_apply, ← decompose_smul,
    smul_eq_mul, mul_one]

