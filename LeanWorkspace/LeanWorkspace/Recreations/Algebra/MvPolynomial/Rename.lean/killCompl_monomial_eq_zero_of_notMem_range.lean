import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem killCompl_monomial_eq_zero_of_notMem_range {s : τ →₀ ℕ} (c : R)
    {a : τ} (ha : a ∈ s.support) (hs : a ∉ Set.range f) :
    (monomial s c).killCompl hf = 0 := by
  rw [MvPolynomial.killCompl, aeval_monomial, Finsupp.prod]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero ha
  simp [hs, zero_pow (Finsupp.mem_support_iff.mp ha)]

