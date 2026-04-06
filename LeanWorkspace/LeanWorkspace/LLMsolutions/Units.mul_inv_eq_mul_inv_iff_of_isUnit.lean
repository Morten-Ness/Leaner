FAIL
import Mathlib

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem mul_inv_eq_mul_inv_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rcases hb with ⟨u, rfl⟩
  rcases hd with ⟨v, rfl⟩
  simpa using u.mul_inv_eq_mul_inv_iff₀ (c := c) (d := v) hbd v.ne_zero
