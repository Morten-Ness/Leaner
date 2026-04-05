import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem induction_on'' {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (MvPolynomial.C : ∀ a, motive (MvPolynomial.C a))
    (monomial_add :
      ∀ (a : σ →₀ ℕ) (b : R) (f : MvPolynomial σ R),
        a ∉ f.support → b ≠ 0 → motive f → motive (MvPolynomial.monomial a b) →
          motive ((MvPolynomial.monomial a b) + f))
    (mul_X : ∀ (p : MvPolynomial σ R) (n : σ), motive p → motive (p * MvPolynomial.X n)) :
    motive p := MvPolynomial.monomial_add_induction_on p MvPolynomial.C fun a b f ha hb hf =>
    monomial_add a b f ha hb hf <| MvPolynomial.induction_on_monomial MvPolynomial.C mul_X a b

