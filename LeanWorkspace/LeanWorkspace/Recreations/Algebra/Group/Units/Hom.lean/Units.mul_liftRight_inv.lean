import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem mul_liftRight_inv {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    f x * ↑(Units.liftRight f g h x)⁻¹ = 1 := by
  rw [Units.mul_inv_eq_iff_eq_mul, one_mul, Units.coe_liftRight]

