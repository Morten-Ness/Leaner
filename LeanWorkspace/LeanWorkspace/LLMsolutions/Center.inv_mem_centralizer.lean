FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable [Group M] {a b : M}

theorem inv_mem_centralizer (ha : a ∈ Set.centralizer S) : a⁻¹ ∈ Set.centralizer S := by
  rw [Set.mem_centralizer_iff] at ha ⊢
  intro x hx
  have hax : x * a = a * x := ha x hx
  calc
    a⁻¹ * x = a⁻¹ * (a * x * a⁻¹) := by
      rw [← hax, mul_assoc, inv_mul_cancel, one_mul]
    _ = (a⁻¹ * a) * x * a⁻¹ := by rw [mul_assoc, mul_assoc]
    _ = x * a⁻¹ := by rw [inv_mul_cancel, one_mul]
