import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_top : ((⊤ : Subgroup G) : Set G) = Set.univ := rfl

