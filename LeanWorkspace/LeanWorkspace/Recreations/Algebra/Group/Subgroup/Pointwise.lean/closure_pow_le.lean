import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem closure_pow_le : ∀ {n}, closure (s ^ n) ≤ closure s
  | 0 => by simp_all
  | n + 1 => by grw [pow_succ, Subgroup.closure_mul_le, closure_pow_le, sup_idem]
