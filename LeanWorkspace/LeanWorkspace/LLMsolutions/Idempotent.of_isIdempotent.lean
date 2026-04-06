import Mathlib

variable {M N S : Type*}

variable [Mul M] {a : M}

theorem of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] : a * a = a := by
  simpa using Std.IdempotentOp.idempotent (α := M) (op := (· * ·)) a
