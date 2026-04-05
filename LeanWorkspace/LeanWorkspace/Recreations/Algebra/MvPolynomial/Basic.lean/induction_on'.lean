import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem induction_on' {P : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (MvPolynomial.monomial : ∀ (u : σ →₀ ℕ) (a : R), P (MvPolynomial.monomial u a))
    (add : ∀ p q : MvPolynomial σ R, P p → P q → P (p + q)) : P p := Finsupp.induction p
    (suffices P (MvPolynomial.monomial 0 0) by rwa [MvPolynomial.monomial_zero] at this
    show P (MvPolynomial.monomial 0 0) from MvPolynomial.monomial 0 0)
    fun _ _ _ _ha _hb hPf => add _ _ (MvPolynomial.monomial _ _) hPf

