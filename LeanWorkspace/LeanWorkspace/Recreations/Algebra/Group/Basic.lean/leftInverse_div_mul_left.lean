import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x ↦ x / c) fun x ↦ x * c := fun x ↦ mul_div_cancel_right x c

