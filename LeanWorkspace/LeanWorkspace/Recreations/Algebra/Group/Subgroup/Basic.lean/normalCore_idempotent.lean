import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_idempotent (H : Subgroup G) : H.normalCore.normalCore = H.normalCore := H.Subgroup.normalCore_eq_self Subgroup.normalCore

