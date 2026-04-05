import Mathlib

variable (R : Type*)

theorem IsSemireal.not_isSumSq_neg_one [AddGroup R] [One R] [Mul R] [IsSemireal R] :
    ¬ IsSumSq (-1 : R) := (by simpa using one_add_ne_zero ·)

