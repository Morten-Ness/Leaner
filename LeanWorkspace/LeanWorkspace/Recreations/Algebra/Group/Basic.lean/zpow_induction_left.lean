import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_induction_left {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (g * a)) (h_inv : ∀ a, P a → P (g⁻¹ * a)) (n : ℤ) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [Int.add_comm, zpow_add, zpow_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [Int.sub_eq_add_neg, Int.add_comm, zpow_add, zpow_neg_one]
    exact h_inv _ ih

