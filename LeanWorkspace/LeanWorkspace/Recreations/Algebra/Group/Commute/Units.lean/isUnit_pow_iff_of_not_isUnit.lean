import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem isUnit_pow_iff_of_not_isUnit (hx : ¬ IsUnit a) {n : ℕ} :
    IsUnit (a ^ n) ↔ n = 0 := by
  rcases n with (_ | n) <;>
  simp [hx]

