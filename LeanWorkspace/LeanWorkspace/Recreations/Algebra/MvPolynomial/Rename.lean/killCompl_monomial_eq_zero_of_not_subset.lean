import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem killCompl_monomial_eq_zero_of_not_subset {s : τ →₀ ℕ} (c : R)
    (hs : ¬ ↑s.support ⊆ Set.range f) : (monomial s c).killCompl hf = 0 := have ⟨_, ha, hs⟩ := Set.not_subset.mp hs
  MvPolynomial.killCompl_monomial_eq_zero_of_notMem_range hf c ha hs

