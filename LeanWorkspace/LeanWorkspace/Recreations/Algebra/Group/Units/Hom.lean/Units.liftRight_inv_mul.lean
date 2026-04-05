import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem liftRight_inv_mul {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    ↑(Units.liftRight f g h x)⁻¹ * f x = 1 := by
  rw [Units.inv_mul_eq_iff_eq_mul, mul_one, Units.coe_liftRight]

