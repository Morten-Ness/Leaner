import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_insert_one (s : Set M) : Submonoid.closure (insert 1 s) = Submonoid.closure s := by
  rw [insert_eq, Submonoid.closure_union, sup_eq_right, Submonoid.closure_singleton_le_iff_mem]
  apply one_mem

