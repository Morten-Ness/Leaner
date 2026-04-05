import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem _root_.AddSubgroup.toSubgroup'_closure (S : Set (Additive G)) :
    (AddSubgroup.closure S).toSubgroup' = Subgroup.closure (Additive.ofMul ⁻¹' S) := congr_arg AddSubgroup.toSubgroup' (Subgroup.toAddSubgroup'_closure _).symm

