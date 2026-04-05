import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

variable {p} (φ : MvPolynomial σ R)

theorem support_expand_subset [DecidableEq σ] :
    (MvPolynomial.expand p φ).support ⊆ φ.support.image (p • ·) := by
  conv_lhs => rw [φ.as_sum]
  simp only [map_sum, MvPolynomial.expand_monomial]
  refine MvPolynomial.support_sum.trans ?_
  aesop (add simp Finset.subset_iff)

