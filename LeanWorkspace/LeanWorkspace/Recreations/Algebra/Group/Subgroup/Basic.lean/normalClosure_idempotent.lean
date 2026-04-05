import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_idempotent : Subgroup.normalClosure ↑(Subgroup.normalClosure s) = Subgroup.normalClosure s := Subgroup.normalClosure_eq_self _

