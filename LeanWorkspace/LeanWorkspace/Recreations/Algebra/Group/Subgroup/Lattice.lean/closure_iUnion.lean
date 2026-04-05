import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_iUnion {ι} (s : ι → Set G) : Subgroup.closure (⋃ i, s i) = ⨆ i, Subgroup.closure (s i) := (Subgroup.gi G).gc.l_iSup

