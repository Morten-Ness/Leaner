import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem zpowers_eq_closure (g : G) : Subgroup.zpowers g = closure {g} := by
  ext
  exact mem_closure_singleton.symm

