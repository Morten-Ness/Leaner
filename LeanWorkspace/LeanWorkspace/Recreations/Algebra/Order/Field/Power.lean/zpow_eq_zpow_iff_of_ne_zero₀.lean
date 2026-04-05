import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem zpow_eq_zpow_iff_of_ne_zero₀ (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n := match n with
  | Int.ofNat m => by
    simp only [Int.ofNat_eq_natCast, ne_eq, Nat.cast_eq_zero, zpow_natCast, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, ne_eq, neg_eq_zero, Nat.cast_eq_zero, zpow_neg, zpow_natCast,
      inv_inj, even_neg, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn

