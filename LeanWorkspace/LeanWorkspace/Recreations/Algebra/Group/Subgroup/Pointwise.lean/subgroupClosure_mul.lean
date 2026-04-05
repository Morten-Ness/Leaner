import Mathlib

open scoped RightActions

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem subgroupClosure_mul (hs : s.Nonempty) : closure s * s = closure s := by
  rw [← Set.iUnion_op_smul_set]
  have h a (ha : a ∈ s) : (closure s : Set G) <• a = closure s :=
    op_smul_coe_set <| subset_closure ha
  simp +contextual [h, hs]

