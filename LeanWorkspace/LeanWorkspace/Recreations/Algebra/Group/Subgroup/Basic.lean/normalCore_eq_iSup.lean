import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalCore_eq_iSup (H : Subgroup G) :
    H.normalCore = ⨆ (N : Subgroup G) (_ : Normal N) (_ : N ≤ H), N := le_antisymm
    (le_iSup_of_le H.normalCore
      (le_iSup_of_le H.normalCore_normal (le_iSup_of_le H.normalCore_le le_rfl)))
    (iSup_le fun _ => iSup_le fun _ => iSup_le Subgroup.normal_le_normalCore.mpr)

