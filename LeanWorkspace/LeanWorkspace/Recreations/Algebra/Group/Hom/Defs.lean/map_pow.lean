import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N]

variable [FunLike F M N]

variable [FunLike F G H]

theorem map_pow [Monoid G] [Monoid H] [MonoidHomClass F G H] (f : F) (a : G) :
    ∀ n : ℕ, f (a ^ n) = f a ^ n
  | 0 => by rw [pow_zero, pow_zero, map_one]
  | n + 1 => by rw [pow_succ, pow_succ, map_mul, map_pow f a n]
