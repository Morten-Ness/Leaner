import Mathlib

variable {M : Type*}

variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

theorem _root_.Units.commute_iff_inv_mul_cancel {u : Mˣ} {a : M} :
    Commute ↑u a ↔ ↑u⁻¹ * a * u = a := by
  rw [mul_assoc, Units.inv_mul_eq_iff_eq_mul, eq_comm, Commute, SemiconjBy]

