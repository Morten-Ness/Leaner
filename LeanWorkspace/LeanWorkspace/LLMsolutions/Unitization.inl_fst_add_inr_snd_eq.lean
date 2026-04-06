FAIL
import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass A] (x : Unitization R A) :
    Unitization.inl x.fst + (x.snd : Unitization R A) = x := by
  cases x using Unitization.rec with
  | h r a =>
      rfl
