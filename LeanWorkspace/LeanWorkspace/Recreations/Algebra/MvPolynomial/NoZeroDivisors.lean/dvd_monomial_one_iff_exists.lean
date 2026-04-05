import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R] [NoZeroDivisors R] {p q r : MvPolynomial σ R}

theorem dvd_monomial_one_iff_exists {n : σ →₀ ℕ} :
    p ∣ monomial n 1 ↔ ∃ m u, m ≤ n ∧ IsUnit u ∧ p = monomial m u := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · suffices ∃ m, m ≤ n by simpa [Subsingleton.elim _ p]
    use n
  rw [MvPolynomial.dvd_monomial_iff_exists (one_ne_zero' R)]
  apply exists_congr
  intro m
  simp_rw [isUnit_iff_dvd_one]

