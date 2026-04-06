import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_mono {H K : Subgroup G} (h : H ≤ K) : H.normalCore ≤ K.normalCore := by
  exact Subgroup.normalCore_mono h
