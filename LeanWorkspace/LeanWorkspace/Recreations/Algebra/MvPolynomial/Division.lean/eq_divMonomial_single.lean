import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem eq_divMonomial_single [IsLeftCancelAdd R]
    {i : σ} {p q r : MvPolynomial σ R} (h : p = X i * q + r)
    (hr : ∀ n ∈ r.support, n i = 0) :
    q = p.divMonomial (Finsupp.single i 1) := by
  ext n
  rw [MvPolynomial.coeff_divMonomial, h, coeff_add, coeff_X_mul, left_eq_add, ← notMem_support_iff]
  intro hn
  simpa using hr _ hn

