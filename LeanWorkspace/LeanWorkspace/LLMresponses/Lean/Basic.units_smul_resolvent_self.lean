FAIL
import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  rw [resolvent, resolvent]
  simp only [Units.smul_def, Algebra.smul_def]
  have hr : algebraMap R A (↑r : R) * algebraMap R A (↑(↑r⁻¹) : R) = 1 := by
    exact map_mul_of_inv _ r
  have hsub :
      algebraMap R A (↑r : R) - a =
        algebraMap R A (↑r : R) * (1 - algebraMap R A (↑(↑r⁻¹) : R) * a) := by
    rw [mul_sub, mul_one, ← mul_assoc, hr, one_mul]
  rw [hsub]
  rw [mul_inv₀]
  simp [hr]
