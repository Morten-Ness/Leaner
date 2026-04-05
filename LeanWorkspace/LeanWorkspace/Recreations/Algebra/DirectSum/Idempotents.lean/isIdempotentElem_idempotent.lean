import Mathlib

variable {R I : Type*} [Semiring R] [DecidableEq I] (V : I → Ideal R) [Decomposition V]

theorem isIdempotentElem_idempotent (i : I) : IsIdempotentElem (DirectSum.idempotent V i : R) := by
  rw [IsIdempotentElem, ← DirectSum.decompose_eq_mul_idempotent, DirectSum.idempotent, decompose_coe, of_eq_same]

