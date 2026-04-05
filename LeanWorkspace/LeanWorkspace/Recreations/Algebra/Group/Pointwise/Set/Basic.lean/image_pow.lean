import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] [Monoid β] [FunLike F α β]

theorem image_pow [MonoidHomClass F α β] (f : F) (s : Set α) : ∀ n, f '' (s ^ n) = (f '' s) ^ n
  | 0 => by simp [Set.singleton_one]
  | n + 1 => Set.image_pow_of_ne_zero n.succ_ne_zero ..
