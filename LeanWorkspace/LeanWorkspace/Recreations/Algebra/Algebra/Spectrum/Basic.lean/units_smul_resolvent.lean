import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) := by
  by_cases h : s ∈ spectrum R a
  · rw [spectrum.mem_iff] at h
    simp only [resolvent, Algebra.algebraMap_eq_smul_one] at *
    rw [smul_assoc, ← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • (1 : A) - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', smul_zero]
  · simp only [resolvent]
    have h' : IsUnit (r • algebraMap R A (r⁻¹ • s) - a) := by
      simpa [Algebra.algebraMap_eq_smul_one, smul_assoc] using spectrum.notMem_iff.mp h
    rw [← h'.val_subInvSMul, ← (spectrum.notMem_iff.mp h).unit_spec, Ring.inverse_unit, Ring.inverse_unit,
      h'.val_inv_subInvSMul]
    simp only [Algebra.algebraMap_eq_smul_one, smul_assoc, smul_inv_smul]

