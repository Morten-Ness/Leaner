import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem mul_subgroupClosure (hs : s.Nonempty) : s * closure s = closure s := by
  rw [← smul_eq_mul, ← Set.iUnion_smul_set]
  have h a (ha : a ∈ s) : a • (closure s : Set G) = closure s :=
    smul_coe_set <| subset_closure ha
  simp +contextual [h, hs]

