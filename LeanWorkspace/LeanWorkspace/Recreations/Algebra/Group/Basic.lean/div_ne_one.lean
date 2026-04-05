import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b := not_congr div_eq_one

