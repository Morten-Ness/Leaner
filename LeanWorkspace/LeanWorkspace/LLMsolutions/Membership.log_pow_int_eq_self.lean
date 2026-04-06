FAIL
import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.natAbs) (m : ℕ) : Submonoid.log (Submonoid.pow x m) = m := by
  rcases Int.natAbs_eq (α := ℤ) x with rfl | rfl
  · simpa [Submonoid.pow] using Nat.log_nat_eq_self h m
  · exfalso
    simpa using h
