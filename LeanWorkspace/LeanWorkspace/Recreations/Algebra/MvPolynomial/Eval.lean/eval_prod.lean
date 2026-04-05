import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {f : σ → R}

theorem eval_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    MvPolynomial.eval g (∏ i ∈ s, f i) = ∏ i ∈ s, MvPolynomial.eval g (f i) := map_prod (MvPolynomial.eval g) _ _

