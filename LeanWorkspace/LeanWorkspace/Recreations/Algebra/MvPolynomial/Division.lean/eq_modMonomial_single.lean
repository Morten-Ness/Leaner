import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem eq_modMonomial_single [IsLeftCancelAdd R]
    {σ : Type*} {i : σ} {p q r : MvPolynomial σ R}
    (h : p = X i * q + r) (hr : ∀ n ∈ r.support, n i = 0) :
    r = p.modMonomial (Finsupp.single i 1) := by
  have h' := id h
  rwa [← MvPolynomial.divMonomial_add_modMonomial_single p i,
    MvPolynomial.eq_divMonomial_single h hr, add_right_inj, eq_comm] at h'

