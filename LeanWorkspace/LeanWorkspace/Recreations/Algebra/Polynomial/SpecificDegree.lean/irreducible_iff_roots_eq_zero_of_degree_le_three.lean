import Mathlib

variable {K : Type*} [Field K] {p : K[X]}

theorem irreducible_iff_roots_eq_zero_of_degree_le_three
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) :
    Irreducible p ↔ p.roots = 0 := by
  have hp0 : p ≠ 0 := by rintro rfl; rw [natDegree_zero] at hp2; cases hp2
  rw [← irreducible_mul_leadingCoeff_inv,
      (monic_mul_leadingCoeff_inv hp0).irreducible_iff_roots_eq_zero_of_degree_le_three,
      mul_comm, roots_C_mul]
  · exact inv_ne_zero (leadingCoeff_ne_zero.mpr hp0)
  · rwa [natDegree_mul_leadingCoeff_inv _ hp0]
  · rwa [natDegree_mul_leadingCoeff_inv _ hp0]

