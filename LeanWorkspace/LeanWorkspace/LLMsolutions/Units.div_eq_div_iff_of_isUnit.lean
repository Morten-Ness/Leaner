FAIL
import Mathlib

variable {M : Type*}

variable [DivisionMonoid M] {a b c d : M}

theorem div_eq_div_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rcases hb with ⟨u, rfl⟩
  rcases hd with ⟨v, rfl⟩
  simp [div_eq_mul_inv, mul_assoc, Units.val_mul, Units.mul_inv, hbd.eq]
