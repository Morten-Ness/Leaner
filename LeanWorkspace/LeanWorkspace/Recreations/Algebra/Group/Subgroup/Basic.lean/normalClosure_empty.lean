import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_empty : Subgroup.normalClosure (∅ : Set G) = (⊥ : Subgroup G) := by
  rw [← Subgroup.normalClosure_closure_eq_normalClosure, closure_empty, Subgroup.normalClosure_eq_self]

