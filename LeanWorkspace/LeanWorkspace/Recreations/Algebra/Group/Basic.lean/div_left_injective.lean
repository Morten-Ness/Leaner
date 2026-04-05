import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_left_injective : Function.Injective fun a ↦ a / b := by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ mul_left_injective b⁻¹ h

