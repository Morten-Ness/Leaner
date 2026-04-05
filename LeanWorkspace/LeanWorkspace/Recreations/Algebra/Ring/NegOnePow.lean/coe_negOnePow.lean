import Mathlib

set_option backward.isDefEq.respectTransparency false in
theorem coe_negOnePow (R : Type*) [Ring R] (n : ℤ) :
    (n.negOnePow : R) = (-1 : R) ^ n.natAbs := by
  cases n with
  | ofNat n => exact Int.cast_negOnePow_natCast R n
  | negSucc n => simp [Int.negOnePow_def, Units.val_pow_eq_pow_val]

