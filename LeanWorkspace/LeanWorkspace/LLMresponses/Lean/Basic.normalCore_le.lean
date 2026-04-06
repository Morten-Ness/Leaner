FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_le (H : Subgroup G) : H.normalCore ≤ H := by
  intro x hx
  change x ∈ sInf {K : Subgroup G | K.Normal ∧ K ≤ H} at hx
  exact Set.mem_iInter.mp hx H (by constructor <;> simp)
