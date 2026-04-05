import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β] [Monoid α] [Monoid β] [FunLike F α β]

theorem image_pow [MonoidHomClass F α β] (f : F) (s : Finset α) : ∀ n, (s ^ n).image f = s.image f ^ n
  | 0 => by simp [Finset.singleton_one]
  | n + 1 => Finset.image_pow_of_ne_zero n.succ_ne_zero ..
