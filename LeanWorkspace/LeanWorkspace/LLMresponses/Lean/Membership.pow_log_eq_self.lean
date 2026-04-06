import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem pow_log_eq_self [DecidableEq M] {n : M} (p : Submonoid.powers n) : Submonoid.pow n (Submonoid.log p) = p := by
  simpa using Submonoid.pow_log_eq_self p
