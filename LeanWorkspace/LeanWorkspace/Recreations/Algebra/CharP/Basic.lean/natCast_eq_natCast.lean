import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

variable [IsRightCancelAdd R]

theorem natCast_eq_natCast : (a : R) = b ↔ a ≡ b [MOD p] := by
  wlog hle : a ≤ b
  · rw [eq_comm, this R p (le_of_not_ge hle), Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' hle, ← cast_eq_zero_iff R p (b - a),
    ← add_right_cancel_iff (G := R) (a := a) (b := b - a), zero_add, ← Nat.cast_add,
    Nat.sub_add_cancel hle, eq_comm]

