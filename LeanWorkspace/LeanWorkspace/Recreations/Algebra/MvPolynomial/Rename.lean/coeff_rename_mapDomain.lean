import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem coeff_rename_mapDomain (f : σ → τ) (hf : Function.Injective f) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (MvPolynomial.rename f φ).coeff (d.mapDomain f) = φ.coeff d := by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial u r =>
    rw [MvPolynomial.rename_monomial, coeff_monomial, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hf).eq_iff]
  | add =>
    simp only [*, map_add, coeff_add]

