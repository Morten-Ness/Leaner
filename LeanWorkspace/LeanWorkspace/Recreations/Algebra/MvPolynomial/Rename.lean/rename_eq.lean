import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

set_option backward.isDefEq.respectTransparency false in
theorem rename_eq (f : σ → τ) (p : MvPolynomial σ R) :
    MvPolynomial.rename f p = Finsupp.mapDomain (Finsupp.mapDomain f) p := by
  simp_rw [MvPolynomial.rename, aeval_def, eval₂, Finsupp.mapDomain, algebraMap_eq, comp_apply,
    X_pow_eq_monomial, ← monomial_finsupp_sum_index, ← single_eq_monomial]

