import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem mul_right_surjective (a : G) : Function.Surjective fun x ↦ x * a := fun x ↦
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

