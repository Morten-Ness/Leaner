import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem toAddSubgroup_closure (S : Set G) :
    (Subgroup.closure S).toAddSubgroup = AddSubgroup.closure (Additive.toMul ⁻¹' S) := le_antisymm (toAddSubgroup.le_symm_apply.mp <|
      (Subgroup.closure_le _).mpr (AddSubgroup.subset_closure (G := Additive G)))
    ((AddSubgroup.closure_le _).mpr (Subgroup.subset_closure (G := G)))

