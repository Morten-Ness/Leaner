import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_induction_right {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (a * g)) (h_inv : ∀ a, P a → P (a * g⁻¹)) (n : ℤ) : P (g ^ n) := by
  induction n with
  | zero => rwa [zpow_zero]
  | succ n ih =>
    rw [zpow_add_one]
    exact h_mul _ ih
  | pred n ih =>
    rw [zpow_sub_one]
    exact h_inv _ ih

