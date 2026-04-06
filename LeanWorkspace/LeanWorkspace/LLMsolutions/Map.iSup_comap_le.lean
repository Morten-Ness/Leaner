import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem iSup_comap_le {ι : Sort*} (f : G →* N) (s : ι → Subgroup N) :
    ⨆ i, (s i).comap f ≤ (iSup s).comap f := by
  refine iSup_le ?_
  intro i
  intro x hx
  exact show f x ∈ iSup s from le_iSup s i hx
