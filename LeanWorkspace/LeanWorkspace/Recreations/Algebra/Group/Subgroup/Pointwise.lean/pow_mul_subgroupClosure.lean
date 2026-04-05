import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem pow_mul_subgroupClosure (hs : s.Nonempty) : ∀ n, s ^ n * closure s = closure s
  | 0 => by simp
  | n + 1 => by rw [pow_succ, mul_assoc, Set.mul_subgroupClosure hs, pow_mul_subgroupClosure hs]
