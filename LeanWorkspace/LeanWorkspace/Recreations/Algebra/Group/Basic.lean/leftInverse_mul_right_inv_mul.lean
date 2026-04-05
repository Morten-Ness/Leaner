import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem leftInverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x ↦ c * x) fun x ↦ c⁻¹ * x := fun x ↦ mul_inv_cancel_left c x

