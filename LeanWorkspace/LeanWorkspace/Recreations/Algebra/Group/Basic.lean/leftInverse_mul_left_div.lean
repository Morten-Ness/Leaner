import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x ↦ x * c) fun x ↦ x / c := fun x ↦ div_mul_cancel x c

