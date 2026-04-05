import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoidWithOne R]

theorem one_eq_closure : (1 : AddSubmonoid R) = closure {1} := by
  rw [closure_singleton_eq, AddSubmonoid.one_eq_mrange]; congr 1; ext; simp

