import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem powers_eq_closure (n : M) : Submonoid.powers n = closure {n} := by
  ext
  exact Submonoid.mem_closure_singleton.symm

