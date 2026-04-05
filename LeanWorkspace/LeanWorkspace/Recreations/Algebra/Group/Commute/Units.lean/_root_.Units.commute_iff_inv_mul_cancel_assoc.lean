import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem _root_.Units.commute_iff_inv_mul_cancel_assoc {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u⁻¹ * (a * u) = a := by
  rw [u.commute_iff_inv_mul_cancel, mul_assoc]

