import Mathlib

open scoped nonZeroDivisors

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀}

theorem mk_mem_nonZeroDivisors_associates : Associates.mk a ∈ (Associates M₀)⁰ ↔ a ∈ M₀⁰ := by
  rw [mem_nonZeroDivisors_iff_right, mem_nonZeroDivisors_iff_right]
  contrapose!
  constructor
  · rintro ⟨⟨x⟩, hx₁, hx₂⟩
    refine ⟨x, ?_, ?_⟩
    · rwa [← Associates.mk_eq_zero, ← Associates.mk_mul_mk, ← Associates.quot_mk_eq_mk]
    · rwa [← Associates.mk_ne_zero, ← Associates.quot_mk_eq_mk]
  · refine fun ⟨b, hb₁, hb₂⟩ ↦ ⟨Associates.mk b, ?_, by rwa [Associates.mk_ne_zero]⟩
    rw [Associates.mk_mul_mk, hb₁, Associates.mk_zero]

