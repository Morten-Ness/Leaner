import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inr_neg [NegZeroClass R] [Neg M] (m : M) : (TrivSqZeroExt.inr (-m) : tsze R M) = -TrivSqZeroExt.inr m := TrivSqZeroExt.ext neg_zero.symm rfl

