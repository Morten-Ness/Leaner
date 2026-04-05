import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem nontrivial_iff : Nontrivial (Subgroup G) ↔ Nontrivial G := not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans Subgroup.subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)

