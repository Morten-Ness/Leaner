FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable [Group M] {a b : M}

theorem div_mem_centralizer (ha : a ∈ Set.centralizer S) (hb : b ∈ Set.centralizer S) :
    a / b ∈ Set.centralizer S := by
  rw [Set.mem_centralizer_iff] at ha hb ⊢
  intro c hc
  rw [div_eq_mul_inv]
  have hb' : b⁻¹ * c = c * b⁻¹ := by
    rw [← mul_inv_rev, hb c hc, mul_inv_rev]
  calc
    (a * b⁻¹) * c = a * (b⁻¹ * c) := by rw [mul_assoc]
    _ = a * (c * b⁻¹) := by rw [hb']
    _ = (a * c) * b⁻¹ := by rw [← mul_assoc]
    _ = (c * a) * b⁻¹ := by rw [ha c hc]
    _ = c * (a * b⁻¹) := by rw [mul_assoc]
