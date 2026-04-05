import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.univ ↔ H = ⊤ := (SetLike.ext'_iff.trans (by rfl)).symm

