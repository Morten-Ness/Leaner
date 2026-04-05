import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => simp
  | succ n ihn => simp only [← Int.add_assoc, zpow_add_one, ihn, mul_assoc]
  | pred n ihn => rw [zpow_sub_one, ← mul_assoc, ← ihn, ← zpow_sub_one, Int.add_sub_assoc]

