import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem _root_.Units.commute_iff_mul_inv_cancel_assoc {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u * (a * ↑u⁻¹) = a := by
  rw [u.commute_iff_mul_inv_cancel, mul_assoc]

