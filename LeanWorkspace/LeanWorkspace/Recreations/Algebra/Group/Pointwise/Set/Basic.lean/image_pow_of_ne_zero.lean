import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] [Monoid β] [FunLike F α β]

theorem image_pow_of_ne_zero [MulHomClass F α β] :
    ∀ {n}, n ≠ 0 → ∀ (f : F) (s : Set α), f '' (s ^ n) = (f '' s) ^ n
  | 1, _ => by simp
  | n + 2, _ => by simp [Set.image_mul, pow_succ _ n.succ, image_pow_of_ne_zero]
