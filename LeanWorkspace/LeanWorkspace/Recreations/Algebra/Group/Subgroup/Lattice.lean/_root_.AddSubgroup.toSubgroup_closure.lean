import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem _root_.AddSubgroup.toSubgroup_closure {A : Type*} [AddGroup A] (S : Set A) :
    (AddSubgroup.closure S).toSubgroup = Subgroup.closure (Multiplicative.toAdd ⁻¹' S) := Subgroup.toAddSubgroup.injective (Subgroup.toAddSubgroup_closure _).symm

