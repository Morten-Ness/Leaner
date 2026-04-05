import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem zpow_eq_neg_zpow_iff₀ (hb : b ≠ 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n := match n with
  | Int.ofNat m => by
    simp [pow_eq_neg_pow_iff, hb]
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, zpow_neg, ← inv_neg, pow_eq_neg_pow_iff hb, inv_inj,
      zpow_natCast]
    simp [parity_simps]

