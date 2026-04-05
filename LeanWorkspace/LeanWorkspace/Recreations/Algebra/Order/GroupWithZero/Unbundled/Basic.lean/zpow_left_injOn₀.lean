import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [LinearOrder G₀] {a b c d : G₀}

variable {m n : ℤ}

variable [PosMulStrictMono G₀] [MulPosMono G₀]

theorem zpow_left_injOn₀ : ∀ {n : ℤ}, n ≠ 0 → {a | 0 ≤ a}.InjOn fun a : G₀ ↦ a ^ n
  | (n + 1 : ℕ), _ => by simpa using mod_cast (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn
  | .negSucc n, _ => by
    simpa using inv_injective.comp_injOn (pow_left_strictMonoOn₀ n.succ_ne_zero).injOn
