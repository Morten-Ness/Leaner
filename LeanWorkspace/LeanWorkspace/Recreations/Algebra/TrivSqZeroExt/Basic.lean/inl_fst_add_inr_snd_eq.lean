import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass M] (x : tsze R M) :
    TrivSqZeroExt.inl x.fst + TrivSqZeroExt.inr x.snd = x := TrivSqZeroExt.ext (add_zero x.1) (zero_add x.2)

