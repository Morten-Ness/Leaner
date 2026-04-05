import Mathlib

variable {R : Type*} [CommSemiring R]

theorem eq_zero_of_homogenize_eq_zero {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n)
    (h : p.homogenize n = 0) :
    p = 0 := by
  ext i
  simp only [coeff_zero]
  rcases le_or_gt i p.natDegree with H | H
  · have : p.coeff i = (p.homogenize n).coeff fun₀ | 0 => i | 1 => n - i := by
      simp [Polynomial.coeff_homogenize, Nat.add_sub_of_le (H.trans hn)]
    simp [this, h]
  · exact coeff_eq_zero_of_natDegree_lt H

