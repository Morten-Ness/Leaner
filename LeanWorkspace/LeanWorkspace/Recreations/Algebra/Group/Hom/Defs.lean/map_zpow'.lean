import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [MulOne M] [MulOne N]

variable [FunLike F M N]

variable [FunLike F G H]

theorem map_zpow' [DivInvMonoid G] [DivInvMonoid H] [MonoidHomClass F G H]
    (f : F) (hf : ∀ x : G, f x⁻¹ = (f x)⁻¹) (a : G) : ∀ n : ℤ, f (a ^ n) = f a ^ n
  | (n : ℕ) => by rw [zpow_natCast, map_pow, zpow_natCast]
  | Int.negSucc n => by rw [zpow_negSucc, hf, map_pow, ← zpow_negSucc]
