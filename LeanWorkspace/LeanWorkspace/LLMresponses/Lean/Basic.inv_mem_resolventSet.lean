FAIL
import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ resolventSet R (a : A)) :
    (↑r⁻¹ : R) ∈ resolventSet R (↑a⁻¹ : A) := by
  change IsUnit (algebraMap R A (↑r⁻¹ : R) - ↑a⁻¹ : A)
  have hunit : IsUnit (algebraMap R A (↑r : R) - ↑a : A) := h
  have h1 : IsUnit (-((↑a⁻¹ : A))) := ⟨-↑a⁻¹, -↑a, by simp, by simp⟩
  have h2 : IsUnit (algebraMap R A (↑r⁻¹ : R)) := by
    refine ⟨algebraMap R A (↑r : R), algebraMap R A (↑r⁻¹ : R), ?_, ?_⟩ <;>
      simp [map_mul]
  have hEq :
      (algebraMap R A (↑r⁻¹ : R) - ↑a⁻¹ : A) =
        (-((↑a⁻¹ : A))) * (algebraMap R A (↑r : R) - ↑a : A) *
          algebraMap R A (↑r⁻¹ : R) := by
    calc
      (algebraMap R A (↑r⁻¹ : R) - ↑a⁻¹ : A)
          = algebraMap R A (↑r⁻¹ : R) - ↑a⁻¹ * ((↑a : A) * algebraMap R A (↑r⁻¹ : R)) := by
              rw [Units.val_mul, one_mul]
      _ = algebraMap R A (↑r⁻¹ : R) - ↑a⁻¹ * (algebraMap R A ((↑r : R) * ↑r⁻¹)) := by
              congr 1
              rw [← map_mul, Units.val_mul, mul_comm]
      _ = algebraMap R A (↑r⁻¹ : R) - ↑a⁻¹ := by simp
      _ = (-((↑a⁻¹ : A))) * (algebraMap R A (↑r : R) - ↑a : A) *
            algebraMap R A (↑r⁻¹ : R) := by
              rw [mul_assoc, sub_mul, neg_mul, neg_mul, Units.inv_mul, one_mul]
              congr 1
              rw [← mul_assoc, ← map_mul, Units.val_mul, map_one, mul_one]
  rw [hEq]
  exact h1.mul (hunit.mul h2)
