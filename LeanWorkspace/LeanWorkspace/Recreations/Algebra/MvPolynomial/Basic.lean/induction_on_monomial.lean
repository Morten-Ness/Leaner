import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem induction_on_monomial {motive : MvPolynomial σ R → Prop}
    (MvPolynomial.C : ∀ a, motive (MvPolynomial.C a))
    (mul_X : ∀ p n, motive p → motive (p * MvPolynomial.X n)) : ∀ s a, motive (MvPolynomial.monomial s a) := by
  intro s a
  apply @Finsupp.induction σ ℕ _ _ s
  · change motive (MvPolynomial.monomial 0 a)
    exact MvPolynomial.C a
  · intro n e p _hpn _he ih
    have : ∀ e : ℕ, motive (MvPolynomial.monomial p a * MvPolynomial.X n ^ e) := by
      intro e
      induction e with
      | zero => simp [ih]
      | succ e e_ih => simp [pow_succ, (mul_assoc _ _ _).symm, mul_X, e_ih]
    simp [add_comm, MvPolynomial.monomial_add_single, this]

