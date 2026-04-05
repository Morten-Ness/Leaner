import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem killCompl_monomial {s} {c : R} [Decidable (↑s.support ⊆ Set.range f)] :
    (monomial s c).killCompl hf =
      if ↑s.support ⊆ Set.range f then monomial (s.comapDomain f hf.injOn) c else 0 := by
  split_ifs with h
  · exact MvPolynomial.killCompl_monomial_eq_monomial_comapDomain_of_subset hf c h
  · exact MvPolynomial.killCompl_monomial_eq_zero_of_not_subset hf c h

