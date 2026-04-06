FAIL
import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) := by
  rw [resolvent, resolvent]
  simp only [Algebra.smul_def, Units.smul_def, map_mul]
  congr 1
  rw [← mul_sub]
  let u : Aˣ :=
    Units.map (algebraMap R A) r
  change ↑u * ((algebraMap R A) s - a)⁻¹ʳ = (↑u⁻¹ * ((algebraMap R A) s - a))⁻¹ʳ
  simpa [u] using Units.val_mul_invRev_eq_invRev (Units.map (algebraMap R A) r) ((algebraMap R A) s - a)
