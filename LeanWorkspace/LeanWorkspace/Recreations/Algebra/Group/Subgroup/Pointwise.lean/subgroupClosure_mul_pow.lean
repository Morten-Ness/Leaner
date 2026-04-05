import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem subgroupClosure_mul_pow (hs : s.Nonempty) : ∀ n, closure s * s ^ n = closure s
  | 0 => by simp
  | n + 1 => by rw [pow_succ', ← mul_assoc, Set.subgroupClosure_mul hs, subgroupClosure_mul_pow hs]
