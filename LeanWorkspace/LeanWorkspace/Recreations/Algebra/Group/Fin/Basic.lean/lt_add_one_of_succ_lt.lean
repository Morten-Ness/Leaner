import Mathlib

variable {n : ℕ}

theorem lt_add_one_of_succ_lt {n : ℕ} [NeZero n] {a : Fin n} (ha : a + 1 < n) : a < a + 1 := by
  rw [lt_def, val_add, coe_ofNat_eq_mod, Nat.add_mod_mod, Nat.mod_eq_of_lt ha]
  lia

