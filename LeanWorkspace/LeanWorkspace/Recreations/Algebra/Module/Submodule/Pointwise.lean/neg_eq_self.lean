import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

theorem neg_eq_self [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M) : -p = p := ext fun _ => p.neg_mem_iff

