FAIL
import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem cast_eq_iff_mod_eq [IsLeftCancelAdd R] : (a : R) = (b : R) ↔ a % p = b % p := by
  constructor
  · intro h
    exact CharP.modEq_iff (R := R) p a b |>.mp h
  · intro h
    exact CharP.modEq_iff (R := R) p a b |>.mpr h
