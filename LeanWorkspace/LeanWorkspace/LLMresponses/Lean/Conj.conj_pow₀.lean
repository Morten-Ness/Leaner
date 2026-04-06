import Mathlib

variable {α : Type*} [GroupWithZero α] {a b : α}

theorem conj_pow₀ {s : ℕ} {a d : α} (ha : a ≠ 0) : (a⁻¹ * d * a) ^ s = a⁻¹ * d ^ s * a := by
  induction s with
  | zero =>
      simp [ha]
  | succ s ih =>
      calc
        (a⁻¹ * d * a) ^ (s + 1)
            = (a⁻¹ * d * a) ^ s * (a⁻¹ * d * a) := by simp [pow_succ]
        _ = (a⁻¹ * d ^ s * a) * (a⁻¹ * d * a) := by rw [ih]
        _ = a⁻¹ * d ^ s * (a * a⁻¹) * d * a := by ac_rfl
        _ = a⁻¹ * d ^ s * 1 * d * a := by rw [mul_inv_cancel₀ ha]
        _ = a⁻¹ * (d ^ s * d) * a := by simp [mul_assoc]
        _ = a⁻¹ * d ^ (s + 1) * a := by simp [pow_succ, mul_assoc]
