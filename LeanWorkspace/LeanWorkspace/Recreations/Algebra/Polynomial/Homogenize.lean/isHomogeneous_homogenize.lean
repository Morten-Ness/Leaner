import Mathlib

variable {R : Type*} [CommSemiring R]

theorem isHomogeneous_homogenize {n : ℕ} (p : R[X]) : (p.homogenize n).IsHomogeneous n := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ ?_
  simp only [Prod.forall, mem_antidiagonal]
  rintro a b rfl
  apply MvPolynomial.isHomogeneous_monomial
  simp [Finsupp.update_eq_add_single]

