import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem div_right_injective : Function.Injective fun a ↦ b / a := by
  -- FIXME see above
  simp only [div_eq_mul_inv]
  exact fun a a' h ↦ inv_injective (mul_right_injective b h)

