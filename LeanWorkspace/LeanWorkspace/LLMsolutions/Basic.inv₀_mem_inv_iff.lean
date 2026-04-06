import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v} [Semifield R] [Ring A] [Algebra R A]

theorem inv₀_mem_inv_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (↑a⁻¹ : A) ↔ r ∈ spectrum R (a : A) := by
  simpa using IsUnit.mem_spectrum_inv_iff (R := R) (a := (a : A)) r (Units.isUnit a)
