FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_mono {s t : Set G} (h : s ⊆ t) : Subgroup.normalClosure s ≤ Subgroup.normalClosure t := by
  rw [Subgroup.normalClosure_eq_iInf]
  rw [Subgroup.normalClosure_eq_iInf]
  exact iInf_le_iInf fun N => iInf_le_iInf fun hNt => iInf_le_iInf fun hsN => hsN.comp h
