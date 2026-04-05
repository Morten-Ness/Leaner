import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_right_inj : a / b = a / c ↔ b = c := div_right_injective.eq_iff

