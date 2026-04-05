import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem leftInverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x ↦ c⁻¹ * x) fun x ↦ c * x := fun x ↦ inv_mul_cancel_left c x

