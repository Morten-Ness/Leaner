import Mathlib

variable {M N S : Type*}

variable [Mul M] {a : M}

theorem of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] (a : M) : IsIdempotentElem a :=
  Std.IdempotentOp.idempotent a

