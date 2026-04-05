import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_add_induction_on {motive : MvPolynomial σ R → Prop} (p : MvPolynomial σ R)
    (MvPolynomial.C : ∀ a, motive (MvPolynomial.C a))
    (monomial_add :
      ∀ (a : σ →₀ ℕ) (b : R) (f : MvPolynomial σ R),
        a ∉ f.support → b ≠ 0 → motive f → motive ((MvPolynomial.monomial a b) + f)) :
    motive p := Finsupp.induction p (MvPolynomial.C_0.rec <| MvPolynomial.C 0) monomial_add

