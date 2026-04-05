import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_eq_one : a / b = 1 ↔ a = b := ⟨eq_of_div_eq_one, fun h ↦ by rw [h, div_self']⟩

alias ⟨_, div_eq_one_of_eq⟩ := div_eq_one

alias ⟨_, sub_eq_zero_of_eq⟩ := sub_eq_zero

