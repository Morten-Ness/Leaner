import Mathlib

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  constructor
  · intro ha
    exact CharP.intCast_eq_zero_iff (R := R) (p := p) a |>.mp ha
  · intro ha
    exact CharP.intCast_eq_zero_iff (R := R) (p := p) a |>.mpr ha
