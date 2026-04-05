import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem _root_.Units.commute_iff_mul_inv_cancel {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u * a * ↑u⁻¹ = a := by
  rw [Units.mul_inv_eq_iff_eq_mul, Commute, SemiconjBy]

