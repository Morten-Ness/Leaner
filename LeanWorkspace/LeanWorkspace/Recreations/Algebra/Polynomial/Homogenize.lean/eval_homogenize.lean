import Mathlib

variable {K : Type*} [Semifield K]

theorem eval_homogenize {p : K[X]} {n : ℕ} (hn : p.natDegree ≤ n) (x : Fin 2 → K) (hx : x 1 ≠ 0) :
    MvPolynomial.eval x (p.homogenize n) = p.eval (x 0 / x 1) * x 1 ^ n := by
  simp only [Polynomial.homogenize, Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hn),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [MvPolynomial.eval_monomial, Finsupp.update_eq_add_single, Finsupp.prod_add_index',
    Finsupp.prod_single_index, Finsupp.prod_single_index, pow_sub₀]
  · ring
  all_goals simp_all [pow_add]

