import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_left_surjective (a : G) : Function.Surjective (a * ·) := fun x ↦ ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

