import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_eq_of_isHomogeneous {p : R[X]} {n : ℕ} {q : MvPolynomial (Fin 2) R}
    (hq : q.IsHomogeneous n) (hpq : MvPolynomial.aeval ![X, 1] q = p) :
    p.homogenize n = q := by
  subst p
  rw [q.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial, ← C_eq_algebraMap,
    Polynomial.homogenize_finsetSum, Polynomial.homogenize_C_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [MvPolynomial.monomial_eq]
  congr 1
  obtain rfl : m.weight 1 = n := hq <| by simpa using hm
  simp [Finsupp.prod_fintype, Finsupp.weight_apply, Finsupp.sum_fintype, Fin.prod_univ_two,
    Fin.sum_univ_two]

