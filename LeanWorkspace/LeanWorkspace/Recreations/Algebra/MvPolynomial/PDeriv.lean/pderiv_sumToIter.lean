import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_sumToIter {σ ι} (p i) :
    (sumToIter R σ ι p).pderiv i = sumToIter R σ ι (p.pderiv (.inl i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | mul_X p n _ => cases n <;> simp_all [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite]

