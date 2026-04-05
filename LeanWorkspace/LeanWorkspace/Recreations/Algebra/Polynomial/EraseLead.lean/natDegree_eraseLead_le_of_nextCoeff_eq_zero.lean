import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem natDegree_eraseLead_le_of_nextCoeff_eq_zero (h : f.nextCoeff = 0) :
    f.eraseLead.natDegree ≤ f.natDegree - 2 := by
  refine natDegree_le_pred (n := f.natDegree - 1) (Polynomial.eraseLead_natDegree_le f) ?_
  rw [nextCoeff_eq_zero, natDegree_eq_zero] at h
  obtain ⟨a, rfl⟩ | ⟨hf, h⟩ := h
  · simp
  rw [Polynomial.eraseLead_coeff_of_ne _ (tsub_lt_self hf zero_lt_one).ne, ← nextCoeff_of_natDegree_pos hf]
  simp [nextCoeff_eq_zero, h, eq_zero_or_pos]

