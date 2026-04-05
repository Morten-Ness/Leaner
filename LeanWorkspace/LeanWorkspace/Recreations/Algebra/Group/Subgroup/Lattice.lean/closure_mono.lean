import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_mono ⦃h k : Set G⦄ (h' : h ⊆ k) : Subgroup.closure h ≤ Subgroup.closure k := (Subgroup.gi G).gc.monotone_l h'

