import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v} [Semifield R] [Ring A] [Algebra R A]

theorem inv₀_mem_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (a : A) ↔ r ∈ spectrum R (↑a⁻¹ : A) := by
  obtain (rfl | hr) := eq_or_ne r 0
  · simp
  · lift r to Rˣ using hr.isUnit
    simp [spectrum.inv_mem_iff]

