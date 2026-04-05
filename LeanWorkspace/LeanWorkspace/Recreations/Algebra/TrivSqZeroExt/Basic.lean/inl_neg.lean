import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inl_neg [Neg R] [NegZeroClass M] (r : R) : (TrivSqZeroExt.inl (-r) : tsze R M) = -TrivSqZeroExt.inl r := TrivSqZeroExt.ext rfl neg_zero.symm

