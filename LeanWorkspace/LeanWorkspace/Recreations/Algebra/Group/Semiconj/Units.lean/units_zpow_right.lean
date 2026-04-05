import Mathlib

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_zpow_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a ↑(x ^ m) ↑(y ^ m)
  | (n : ℕ) => by simp only [zpow_natCast, Units.val_pow_eq_pow_val, h, pow_right]
  | -[n+1] => by simp only [zpow_negSucc, Units.val_pow_eq_pow_val, SemiconjBy.units_inv_right, h, pow_right]
