import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem normal_iInf_normal {ι : Sort*} {a : ι → Subgroup G}
    (norm : ∀ i : ι, (a i).Normal) : (iInf a).Normal := by
  constructor
  intro g g_in_iInf h
  rw [Subgroup.mem_iInf] at g_in_iInf ⊢
  intro i
  exact (norm i).conj_mem g (g_in_iInf i) h

