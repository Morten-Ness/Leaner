FAIL
import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_pow_mul_eq_iff_eq_mul {a : M₀} (b c : M₀) (ha : IsUnit a) {k : ℕ} :
    a⁻¹ʳ ^ k * b = c ↔ b = a ^ k * c := by
  rcases ha with ⟨u, rfl⟩
  change ((↑u : M₀)⁻¹ʳ ^ k) * b = c ↔ b = (↑u : M₀) ^ k * c
  rw [show ((↑u : M₀)⁻¹ʳ ^ k) = (((u⁻¹ : M₀ˣ) : M₀) ^ k) by rfl]
  constructor
  · intro h
    calc
      b = ((u : M₀ˣ) ^ k : M₀ˣ) * ((((u⁻¹ : M₀ˣ) : M₀) ^ k) * b) := by
            simp [mul_assoc]
      _ = (u : M₀ˣ) ^ k * c := by rw [h]
      _ = (↑u : M₀) ^ k * c := by rfl
  · intro h
    calc
      (((u⁻¹ : M₀ˣ) : M₀) ^ k) * b = (((u⁻¹ : M₀ˣ) : M₀) ^ k) * ((↑u : M₀) ^ k * c) := by rw [h]
      _ = ((((u⁻¹ : M₀ˣ) : M₀) ^ k) * (↑u : M₀) ^ k) * c := by rw [mul_assoc]
      _ = (((((u⁻¹ : M₀ˣ) * u) : M₀ˣ) : M₀) ^ k) * c := by rw [← Units.val_mul, ← mul_pow]
      _ = c := by simp
