import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) : Polynomial.C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  constructor
  · rintro ⟨φ, rfl⟩ c
    rw [Polynomial.coeff_C_mul]
    apply dvd_mul_right
  · intro h
    choose c hc using h
    classical
      let c' : ℕ → R := fun i => if i ∈ φ.support then c i else 0
      let ψ : R[X] := ∑ i ∈ φ.support, monomial i (c' i)
      use ψ
      ext i
      simp only [c', ψ, Polynomial.coeff_C_mul, mem_support_iff, coeff_monomial, Polynomial.finset_sum_coeff,
        Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [Classical.not_not] at hi
        rwa [mul_zero]

