FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable [Monoid M]

theorem units_inv_mem_center {a : Mˣ} (ha : ↑a ∈ Set.center M) : ↑a⁻¹ ∈ Set.center M := by
  rw [Set.mem_center_iff] at ha ⊢
  intro b
  have h := ha b
  calc
    ↑a⁻¹ * b = ↑a⁻¹ * (b * ↑a) * ↑a⁻¹ := by
      rw [← mul_assoc, h, mul_assoc, Units.val_inv_eq_inv_val, Units.mul_inv, mul_one]
    _ = b * ↑a * ↑a⁻¹ * ↑a⁻¹ := by rw [mul_assoc]
    _ = b * (↑a * ↑a⁻¹) := by rw [← mul_assoc, ← mul_assoc]
    _ = b := by rw [Units.val_inv_eq_inv_val, Units.mul_inv, mul_one]
    _ = b * 1 := by rw [mul_one]
    _ = b * (↑a⁻¹ * ↑a) := by rw [Units.val_inv_eq_inv_val, Units.inv_mul]
    _ = b * ↑a⁻¹ * ↑a := by rw [mul_assoc]
