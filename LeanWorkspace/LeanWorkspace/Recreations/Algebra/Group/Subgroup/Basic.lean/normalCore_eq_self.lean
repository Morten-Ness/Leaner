import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_eq_self (H : Subgroup G) [H.Normal] : H.normalCore = H := le_antisymm H.normalCore_le (Subgroup.normal_le_normalCore.mpr le_rfl)

