import Mathlib

variable {M G : Type*}

variable [Group G] [IsMulTorsionFree G] {n : ℤ} {a b : G}

theorem zpow_left_injective : ∀ {n : ℤ}, n ≠ 0 → Function.Injective fun a : G ↦ a ^ n
  | (n + 1 : ℕ), _ => by
    simpa [← Int.natCast_one, ← Int.natCast_add] using pow_left_injective n.succ_ne_zero
  | .negSucc n, _ => by simpa using inv_injective.comp (pow_left_injective n.succ_ne_zero)
