import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem C_dvd_iff_dvd_coeff (r : R) (φ : MvPolynomial σ R) : MvPolynomial.C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [MvPolynomial.coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose MvPolynomial.C hc using h
    classical
      let c' : (σ →₀ ℕ) → R := fun i => if i ∈ φ.support then MvPolynomial.C i else 0
      let ψ : MvPolynomial σ R := ∑ i ∈ φ.support, MvPolynomial.monomial i (c' i)
      use ψ
      apply MvPolynomial.ext
      intro i
      simp only [ψ, c', MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [MvPolynomial.notMem_support_iff] at hi
        rwa [mul_zero]

