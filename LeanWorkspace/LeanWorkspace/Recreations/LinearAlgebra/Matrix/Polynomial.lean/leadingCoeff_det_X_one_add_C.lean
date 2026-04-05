import Mathlib

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

theorem leadingCoeff_det_X_one_add_C (A : Matrix n n α) :
    leadingCoeff (det ((Polynomial.X : α[Polynomial.X]) • (1 : Matrix n n α[Polynomial.X]) + A.map Polynomial.C)) = 1 := by
  cases subsingleton_or_nontrivial α
  · simp [eq_iff_true_of_subsingleton]
  rw [← @det_one n, ← Polynomial.coeff_det_X_add_C_card _ A, leadingCoeff]
  simp only [Matrix.map_one, C_eq_zero, map_one]
  rcases (Polynomial.natDegree_det_X_add_C_le 1 A).eq_or_lt with h | h
  · simp only [map_one, Matrix.map_one, C_eq_zero] at h
    rw [h]
  · -- contradiction. we have a hypothesis that the degree is less than |n|
    -- but we know that coeff _ n = 1
    have H := coeff_eq_zero_of_natDegree_lt h
    rw [Polynomial.coeff_det_X_add_C_card] at H
    simp at H

