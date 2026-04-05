import Mathlib

variable {α : Type*}

variable {α : Type*} [Monoid α]

variable [Preorder α] [CanonicallyOrderedMul α] [MulRightMono α]

theorem Ici_pow_eq {a : α} :
    ∀ n ≠ 0, Ici a ^ n = Ici (a ^ n)
  | 1, _ => by simp
  | n + 2, _ => by simp [pow_succ _ n.succ, Ici_pow_eq, Set.Ici_mul_Ici_eq]
