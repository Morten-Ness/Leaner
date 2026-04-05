import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem induction_on {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (MvPolynomial.C : ∀ a, motive (MvPolynomial.C a))
    (add : ∀ p q, motive p → motive q → motive (p + q))
    (mul_X : ∀ p n, motive p → motive (p * MvPolynomial.X n)) : motive p := MvPolynomial.induction_on'' p MvPolynomial.C (fun a b f _ha _hb hf hm => add (MvPolynomial.monomial a b) f hm hf) mul_X

