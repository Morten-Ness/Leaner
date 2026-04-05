import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β] [Monoid α] [Monoid β] [FunLike F α β]

theorem image_pow_of_ne_zero [MulHomClass F α β] :
    ∀ {n}, n ≠ 0 → ∀ (f : F) (s : Finset α), (s ^ n).image f = s.image f ^ n
  | 1, _ => by simp
  | n + 2, _ => by simp [Finset.image_mul, pow_succ _ n.succ, image_pow_of_ne_zero]
