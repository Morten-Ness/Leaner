import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem monomial_sum_index {α : Type*} (s : Finset α) (f : α → σ →₀ ℕ) (a : R) :
    MvPolynomial.monomial (∑ i ∈ s, f i) a = MvPolynomial.C a * ∏ i ∈ s, MvPolynomial.monomial (f i) 1 := by
  rw [← MvPolynomial.monomial_sum_one, MvPolynomial.C_mul', ← (MvPolynomial.monomial _).map_smul, smul_eq_mul, mul_one]

